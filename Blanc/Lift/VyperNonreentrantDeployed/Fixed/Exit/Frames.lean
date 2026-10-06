import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Run
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Root
import Blanc.Lift.NodeWalkFrames

/-!
# V+ V5: what every derivation does at each frame of `remove_liquidity`

`Witness2/Frames.lean`'s frame lemmas for the reachable run: for every derivation, a node at a
frame's start configuration has the frame's outcome, raw frame descendants and hash-policy
facts.  Each lemma is stated for the frame's machine under any covered fork and the real
original state `world8` (`(eX.sta.withFork g).withOrig world8`), transported from the kernel
facts of `Run.lean` by `Blanc/Lift/NodeWalkOrig.lean` (`walk_re`, `*Spawn_re`, `settle_re`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2 (okNoRel okNoBody settleOr)
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

attribute [local irreducible] cTop1 cpTop eB cB1 cB2 cpBal eBal cBal1 dBal dB3 cB4 cpEth eRcv
  cRcv1 cpCb eCb cCb1 cpRe eRe cRe1 cRe2 dRe dCb2 cCb3 dCb dRcv2 cRcv3 dRcv dB5 cB6 cpXf eXf
  cXf1 dXf dB7 cB8 dB dTop2 cTop3 dTop

/-- The real machine of a kernel frame: any covered fork, the checkpoint as original state. -/
abbrev reS (s : Sevm) (g : Fork) : Sevm := (s.withFork g).withOrig world8

/-- What the reentrant pool frame `G` does: it reverts; no node of it is at a guarded body
start and every node of its chain satisfies the hash policy `.avoid 0`; its chain reaches the
lock check (pc 0x53) and then the revert pad 0x477e. -/
def ReFacts (G : Exec.Deriv) : Prop :=
  G.exn = .error (.revert, dRe) ∧
    (∀ y, ParentPrefix G y → (HashPol.avoid 0).NodeOK code y ∧ y.pc ∉ lockBodies) ∧
    ∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e

/-- **The reentrant pool frame**: it reads the held lock at the check (pc 0x53), lands on the
revert pad 0x477e and reverts, with no raw frame descendant. -/
theorem frameRe {fk : Fork} (hg : CoveredFork fk) (hs : ReOK world8 eRe.sta) (hag : PAgree cRe0) :
    ∀ G, NodeAt (reS eRe.sta fk) cRe0 G → ReFacts G ∧ Exec.rawFrameDescendants G.exc = [] := by
  intro G hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eReF, wRe1, pRe1, wRe2, pRe2, wRe3, -⟩ := exitFacts
  have hcode : (reS eRe.sta fk).code = code :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eReF).2).2).1
  have w1 := (walk_re hs hg (.avoid 0) codeTries okNoBody 26 cRe0).trans wRe1
  have w2 := (walk_re hs hg (.avoid 0) codeTries okNoBody 6 cRe1).trans wRe2
  have w3 := (walk_re hs hg (.avoid 0) codeTries okNoBody 4 cRe2).trans wRe3
  obtain ⟨hag1, h1⟩ := pwalkH_cont (.avoid 0) codeTries hcode okNoBody 26 cRe0 cRe1 hag w1
  obtain ⟨x1, hx1, hp1, ex1, ds1, bet1⟩ := h1 G hG
  obtain ⟨hag2, h2⟩ := pwalkH_cont (.avoid 0) codeTries hcode okNoBody 6 cRe1 cRe2 hag1 w2
  obtain ⟨x2, hx2, hp2, ex2, ds2, bet2⟩ := h2 x1 hx1
  obtain ⟨ex3, ds3, all3⟩ :=
    pwalkH_halt (.avoid 0) codeTries hcode okNoBody 4 cRe2 _ hag2 w3 x2 hx2
  have hall := chain_trans hp1 bet1 (chain_trans hp2 bet2 all3)
  refine ⟨⟨by rw [← ex1, ← ex2]; exact ex3, fun y hy => ?_, x1, x2, hp1, hx1.1.trans pRe1, hp2,
    hx2.1.trans pRe2⟩, by rw [← ds1, ← ds2]; exact ds3⟩
  obtain ⟨hok, hpol⟩ := hall y hy
  exact ⟨hpol, by simpa only [okNoBody, List.contains_eq_mem, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] using hok⟩

/-- **The callback forwarder frame**: it forwards the receiver's call by `DELEGATECALL`,
spawning the reentrant pool frame, resumes from its failure and reverts. -/
theorem frameCb {fk : Fork} (hg : CoveredFork fk) (hs : ReOK world8 eCb.sta) (hag : PAgree cCb0) :
    ∀ Q, NodeAt (reS eCb.sta fk) cCb0 Q → Q.exn = .error (.revert, dCb) ∧
      ∃ r, NodeAt (reS eRe.sta fk) cRe0 r ∧ Exec.rawFrameDescendants Q.exc = [r] ∧
        ReFacts r := by
  intro Q hQ
  obtain ⟨-, -, -, -, dCb1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eCbF, wCb1, pCb1, dcallRe, caRe, enterRe, -, -, -, -, -, -, setRe, resCb, wCb3, wCb4, -⟩ := exitFacts
  have hcode : (reS eCb.sta fk).code = fwd :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eCbF).2).2).1
  have hsRe : ReOK world8 eRe.sta :=
    ReOK.of_stat ((frameEnterS_stat enterRe).trans (dcallPrep_stat dcallRe).2) hs
  obtain ⟨sRe, nRe⟩ := dcallSpawn_re hs hg dcallRe
    (Frame.precompNeutral_of_codeAddress caRe (by decide) (by decide)) enterRe
  have settleRe : (cpRe.re fk world8).f.settle (.error (.revert, dRe)) =
      .ok (settleOr cpRe.f (.error (.revert, dRe))) :=
    (settle_re hs hg (dcallPrep_stat dcallRe) _).trans setRe
  have w1 := (walk_re hs hg .refuse fwdTries okAny 11 cCb0).trans wCb1
  have w3 := (walk_re hs hg .refuse fwdTries okAny 9 cCb2).trans wCb3
  have w4 := (walk_re hs hg .refuse fwdTries okAny 1 cCb3).trans wCb4
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse fwdTries hcode okAny 11 cCb0 cCb1 hag w1
  obtain ⟨q1, hq1, hp1, ex1, ds1, -⟩ := h1 Q hQ
  have hat : Ninst.At (reS eCb.sta fk).code cCb1.pc (.exec .delegatecall) := by
    rw [hcode, pCb1]; exact decodeT_sound fwdTries dCb1
  obtain ⟨hstep, hent, -, hagRe, hF⟩ := delegatecall_node hag1 hat sRe nRe
  obtain ⟨r, x', sp, hr, e, hx', hexn, hdesc, hagx⟩ :=
    spawn_resume_err (e := .revert) hq1 hag1 hF hstep hent (.inl rfl) settleRe resCb
      (fun G hG => (frameRe hg hsRe (pagree_re hagRe) G (nodeAt_re hG)).1.1)
  have dsg := (frameRe hg hsRe (pagree_re hagRe) r (nodeAt_re hr)).2
  obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse fwdTries hcode okAny 9 cCb2 cCb3 hagx w3
  obtain ⟨q3, hq3, -, ex3, ds3, -⟩ := h3 x' hx'
  obtain ⟨ex4, ds4, -⟩ := pwalkH_halt .refuse fwdTries hcode okAny 1 cCb3 _ hag3 w4 q3 hq3
  refine ⟨by rw [← ex1, ← hexn, ← ex3]; exact ex4, r, nodeAt_re hr, ?_, (frameRe hg hsRe (pagree_re hagRe) r (nodeAt_re hr)).1⟩
  rw [← ds1, hdesc, dsg, ← ds3, ds4]
  rfl

/-- **The receiver frame**: it calls the clone with the reentry calldata and the 100 wei,
spawning `cb` (and below it the reentrant frame), ignores its failure, and stops. -/
theorem frameRcv {fk : Fork} (hg : CoveredFork fk) (hs : ReOK world8 eRcv.sta)
    (hag : PAgree cRcv0) :
    ∀ Xn, NodeAt (reS eRcv.sta fk) cRcv0 Xn → Xn.exn = .ok dRcv ∧
      ChildAgree dRcv cRcv3.keys cRcv3.adrs cRcv3.stor cRcv3.acs ∧
      ∃ q r, NodeAt (reS eCb.sta fk) cCb0 q ∧ NodeAt (reS eRe.sta fk) cRe0 r ∧
        Exec.rawFrameDescendants Xn.exc = [q, r] ∧ Exec.rawFrameDescendants q.exc = [r] ∧
        ReFacts r := by
  intro Xn hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eRcvF, wRcv1, pRcv1, dRcv1, callCb, caCb, enterCb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, setCb, resRcv, wRcv3, wRcv4, -⟩ := exitFacts
  have hcode : (reS eRcv.sta fk).code = Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eRcvF).2).2).1
  have hsCb : ReOK world8 eCb.sta :=
    ReOK.of_stat ((frameEnterS_stat enterCb).trans (callPrepP_stat callCb).2) hs
  obtain ⟨sCb, nCb⟩ := callSpawn_re hs hg callCb
    (Frame.precompNeutral_of_codeAddress caCb (by decide) (by decide)) enterCb
  have settleCb : (cpCb.re fk world8).f.settle (.error (.revert, dCb)) =
      .ok (settleOr cpCb.f (.error (.revert, dCb))) :=
    (settle_re hs hg (callPrepP_stat callCb) _).trans setCb
  have w1 := (walk_re hs hg .refuse recvTries okAny 17 cRcv0).trans wRcv1
  have w3 := (walk_re hs hg .refuse recvTries okAny 1 cRcv2).trans wRcv3
  have w4 := (walk_re hs hg .refuse recvTries okAny 1 cRcv3).trans wRcv4
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse recvTries hcode okAny 17 cRcv0 cRcv1 hag w1
  obtain ⟨x1, hx1, hp1, ex1, ds1, -⟩ := h1 Xn hX
  have hat : Ninst.At (reS eRcv.sta fk).code cRcv1.pc (.exec .call) := by
    rw [hcode, pRcv1]; exact decodeT_sound recvTries dRcv1
  obtain ⟨hstep, hent, -, hagCb, hF⟩ := call_node hag1 hat sCb nCb
  obtain ⟨q, x', sp, hq, e, hx', hexn, hdesc, hagx⟩ :=
    spawn_resume_err (e := .revert) hx1 hag1 hF hstep hent (.inl rfl) settleCb resRcv
      (fun Q hQ => (frameCb hg hsCb (pagree_re hagCb) Q (nodeAt_re hQ)).1)
  obtain ⟨-, r, hr, dsq, hre⟩ := frameCb hg hsCb (pagree_re hagCb) q (nodeAt_re hq)
  obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse recvTries hcode okAny 1 cRcv2 cRcv3 hagx w3
  obtain ⟨x3, hx3, -, ex3, ds3, -⟩ := h3 x' hx'
  obtain ⟨ex4, ds4, -⟩ := pwalkH_halt .refuse recvTries hcode okAny 1 cRcv3 _ hag3 w4 x3 hx3
  refine ⟨by rw [← ex1, ← hexn, ← ex3]; exact ex4, halt1_childAgree recvTries hag3 w4,
    q, r, nodeAt_re hq, hr, ?_, dsq, hre⟩
  rw [← ds1, hdesc, dsq, ← ds3, ds4]
  rfl

/-- **The token's `balanceOf(P)` frame**: a leaf. -/
theorem frameBal {fk : Fork} (hg : CoveredFork fk) (hs : ReOK world8 eBal.sta)
    (hag : PAgree cBal0) :
    ∀ t, NodeAt (reS eBal.sta fk) cBal0 t → t.exn = .ok dBal ∧
      Exec.rawFrameDescendants t.exc = [] ∧
      ChildAgree dBal cBal1.keys cBal1.adrs cBal1.stor cBal1.acs := by
  intro t ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eBalF, wBal1, wBal2, -⟩ := exitFacts
  have hcode : (reS eBal.sta fk).code = Blanc.Lift.VyperNonreentrantDeployed.Token20.code :=
    (Prod.mk.inj (Prod.mk.inj eBalF).2).2
  have w1 := (walk_re hs hg (.avoid 0) tokenTries okAny 29 cBal0).trans wBal1
  have w2 := (walk_re hs hg (.avoid 0) tokenTries okAny 1 cBal1).trans wBal2
  obtain ⟨hca, hall⟩ := leaf_frame_ok (.avoid 0) tokenTries hcode okAny hag w1 w2
  obtain ⟨ex, ds, -⟩ := hall t ht
  exact ⟨ex, ds, hca⟩

/-- **The token's `transfer(R, 100)` frame**: a leaf returning the word 1. -/
theorem frameXf {fk : Fork} (hg : CoveredFork fk) (hs : ReOK world8 eXf.sta)
    (hag : PAgree cXf0) :
    ∀ t, NodeAt (reS eXf.sta fk) cXf0 t → t.exn = .ok dXf ∧
      Exec.rawFrameDescendants t.exc = [] ∧
      ChildAgree dXf cXf1.keys cXf1.adrs cXf1.stor cXf1.acs := by
  intro t ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eXfF, wXf1, wXf2, -⟩ := exitFacts
  have hcode : (reS eXf.sta fk).code = Blanc.Lift.VyperNonreentrantDeployed.Token20.code :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eXfF).2).2).1
  have w1 := (walk_re hs hg (.avoid 0) tokenTries okAny 53 cXf0).trans wXf1
  have w2 := (walk_re hs hg (.avoid 0) tokenTries okAny 1 cXf1).trans wXf2
  obtain ⟨hca, hall⟩ := leaf_frame_ok (.avoid 0) tokenTries hcode okAny hag w1 w2
  obtain ⟨ex, ds, -⟩ := hall t ht
  exact ⟨ex, ds, hca⟩

/-- **The pool body frame**: from the body start of `remove_liquidity` (pc 0x1bae, after the
lock set) it makes, with no release `SSTORE` before, the `STATICCALL` of `balanceOf` (token
frame `t1`), the ETH `CALL` `h` of pc 7427 (the receiver frame `xr`, which spawns `q` and below
it `G`), the token's `transfer` (`t2`), and returns; every node of its chain satisfies the hash
policy `.avoid 0`. -/
theorem frameB {fk : Fork} (hfk : CoveredFork fk) (hs : ReOK world8 eB.sta) (hag : PAgree cB0) :
    ∀ F, NodeAt (reS eB.sta fk) cB0 F → F.exn = .ok dB ∧
      ChildAgree dB cB8.keys cB8.adrs cB8.stor cB8.acs ∧
      ∃ b h t1 xr q G t2 : Exec.Deriv,
        ParentPrefix F b ∧ b.pc = 0x1bae ∧ ParentPrefix b h ∧ h.pc = 7427 ∧
        Ninst.At h.sevm.code h.pc (.exec .call) ∧
        (∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h → x.pc ∉ lockReleasePcs) ∧
        Spawns h xr ∧ NodeAt (reS eBal.sta fk) cBal0 t1 ∧
        NodeAt (reS eRcv.sta fk) cRcv0 xr ∧
        NodeAt (reS eCb.sta fk) cCb0 q ∧ NodeAt (reS eRe.sta fk) cRe0 G ∧
        NodeAt (reS eXf.sta fk) cXf0 t2 ∧
        Exec.rawFrameDescendants F.exc = [t1, xr, q, G, t2] ∧
        Exec.rawFrameDescendants xr.exc = [q, G] ∧ Exec.rawFrameDescendants q.exc = [G] ∧
        ReFacts G ∧ (∀ y, ParentPrefix F y → (HashPol.avoid 0).NodeOK code y) := by
  intro F hF
  obtain ⟨-, -, -, -, -, -, -, eBF, -, walkB1, pB1, walkB2, pB2, decB2, scallBal, caBal, enterBal, -, -, -, balErr, resB3, walkB4, pB4, decB4, callEth, caEth, enterRcv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rcvErr, resB5, walkB6, pB6, decB6, callXf, caXf, enterXf, -, -, -, xfErr, resB7, walkB8, walkB9, -⟩ := exitFacts
  have hcode : (reS eB.sta fk).code = code := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eBF).2).2).1
  have hsBal : ReOK world8 eBal.sta :=
    ReOK.of_stat ((frameEnterS_stat enterBal).trans (scallPrep_stat scallBal).2) hs
  have hsRcv : ReOK world8 eRcv.sta :=
    ReOK.of_stat ((frameEnterS_stat enterRcv).trans (callPrepP_stat callEth).2) hs
  have hsXf : ReOK world8 eXf.sta :=
    ReOK.of_stat ((frameEnterS_stat enterXf).trans (callPrepP_stat callXf).2) hs
  obtain ⟨sBal, nBal⟩ := scallSpawn_re hs hfk scallBal
    (Frame.precompNeutral_of_codeAddress caBal (by decide) (by decide)) enterBal
  obtain ⟨sEth, nRcv⟩ := callSpawn_re hs hfk callEth
    (Frame.precompNeutral_of_codeAddress caEth (by decide) (by decide)) enterRcv
  obtain ⟨sXf, nXf⟩ := callSpawn_re hs hfk callXf
    (Frame.precompNeutral_of_codeAddress caXf (by decide) (by decide)) enterXf
  have wB1 := (walk_re hs hfk (.avoid 0) codeTries okAny 174 cB0).trans walkB1
  have wB2 := (walk_re hs hfk (.avoid 0) codeTries okNoRel 57 cB1).trans walkB2
  have wB4 := (walk_re hs hfk (.avoid 0) codeTries okNoRel 151 cB3).trans walkB4
  have wB6 := (walk_re hs hfk (.avoid 0) codeTries okAny 119 cB5).trans walkB6
  have wB8 := (walk_re hs hfk (.avoid 0) codeTries okAny 125 cB7).trans walkB8
  have wB9 := (walk_re hs hfk (.avoid 0) codeTries okAny 1 cB8).trans walkB9
  have nokAt : ∀ (x : Exec.Deriv) (c : PCfg) (X : Xinst), NodeAt (reS eB.sta fk) c x →
      Ninst.At (reS eB.sta fk).code c.pc (.exec X) → (HashPol.avoid 0).NodeOK code x := by
    intro x c X hx hat
    apply HashPol.nodeOK_of_noKeccak
    have := noKeccakAt_of_exec hat
    rw [hcode] at this
    rw [hx.1]
    exact this
  -- the body start, and the `STATICCALL` of `balanceOf`
  obtain ⟨hag1, h1⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 174 cB0 cB1 hag wB1
  obtain ⟨x1, hx1, pp01, ex01, ds01, bet01⟩ := h1 F hF
  obtain ⟨hag2, h2⟩ := pwalkH_cont (.avoid 0) codeTries hcode okNoRel 57 cB1 cB2 hag1 wB2
  obtain ⟨x2, hx2, pp12, ex12, ds12, bet12⟩ := h2 x1 hx1
  have hat2 : Ninst.At (reS eB.sta fk).code cB2.pc (.exec .staticcall) := by
    rw [hcode, pB2]; exact decodeT_sound codeTries decB2
  obtain ⟨step2, ent2, -, hagBal⟩ := staticcall_node hag2 hat2 sBal nBal
  have hF2 := (scallPrep_node_facts hag2 sBal).2
  obtain ⟨t1, x3, sp1, ht1, e3, hx3, ex3, hdesc3, hag3⟩ :=
    spawn_resume_ok hx2 hag2 hF2 step2 ent2 balErr resB3
      (fun t ht => let r := frameBal hfk hsBal (pagree_re hagBal) t (nodeAt_re ht); ⟨r.1, r.2.2⟩)
  have dst1 := (frameBal hfk hsBal (pagree_re hagBal) t1 (nodeAt_re ht1)).2.1
  -- the ETH `CALL` of pc 7427
  obtain ⟨hag4, h4⟩ := pwalkH_cont (.avoid 0) codeTries hcode okNoRel 151 cB3 cB4 hag3 wB4
  obtain ⟨x4, hx4, pp34, ex34, ds34, bet34⟩ := h4 x3 hx3
  have hat4 : Ninst.At (reS eB.sta fk).code cB4.pc (.exec .call) := by
    rw [hcode, pB4]; exact decodeT_sound codeTries decB4
  obtain ⟨step4, ent4, -, hagRcv, hF4⟩ := call_node hag4 hat4 sEth nRcv
  obtain ⟨xr, x5, sp2, hxr, e5, hx5, ex5, hdesc5, hag5⟩ :=
    spawn_resume_ok hx4 hag4 hF4 step4 ent4 rcvErr resB5
      (fun X hX => let r := frameRcv hfk hsRcv (pagree_re hagRcv) X (nodeAt_re hX); ⟨r.1, r.2.1⟩)
  obtain ⟨-, -, q, G, hq, hG, dsr, dsq, hre⟩ := frameRcv hfk hsRcv (pagree_re hagRcv) xr (nodeAt_re hxr)
  -- the token's `transfer`
  obtain ⟨hag6, h6⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 119 cB5 cB6 hag5 wB6
  obtain ⟨x6, hx6, pp56, ex56, ds56, bet56⟩ := h6 x5 hx5
  have hat6 : Ninst.At (reS eB.sta fk).code cB6.pc (.exec .call) := by
    rw [hcode, pB6]; exact decodeT_sound codeTries decB6
  obtain ⟨step6, ent6, -, hagXf, hF6⟩ := call_node hag6 hat6 sXf nXf
  obtain ⟨t2, x7, sp3, ht2, e7, hx7, ex7, hdesc7, hag7⟩ :=
    spawn_resume_ok hx6 hag6 hF6 step6 ent6 xfErr resB7
      (fun t ht => let r := frameXf hfk hsXf (pagree_re hagXf) t (nodeAt_re ht); ⟨r.1, r.2.2⟩)
  have dst2 := (frameXf hfk hsXf (pagree_re hagXf) t2 (nodeAt_re ht2)).2.1
  -- `RETURN`
  obtain ⟨hag8, h8⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 125 cB7 cB8 hag7 wB8
  obtain ⟨x8, hx8, pp78, ex78, ds78, bet78⟩ := h8 x7 hx7
  obtain ⟨ex9, ds9, all8⟩ := pwalkH_halt (.avoid 0) codeTries hcode okAny 1 cB8 _ hag8 wB9 x8 hx8
  have exF : F.exn = .ok dB := by
    rw [← ex01, ← ex12, ← ex3, ← ex34, ← ex5, ← ex56, ← ex7, ← ex78]; exact ex9
  have dsF : Exec.rawFrameDescendants F.exc = [t1, xr, q, G, t2] := by
    rw [← ds01, ← ds12, hdesc3, dst1, ← ds34, hdesc5, dsr, ← ds56, hdesc7, dst2, ← ds78, ds9]
    rfl
  -- every node of the chain satisfies the hash policy
  have H8 : ∀ y, ParentPrefix x8 y → (HashPol.avoid 0).NodeOK code y := fun y hy => (all8 y hy).2
  have H7 := chain_trans (P := fun y => (HashPol.avoid 0).NodeOK code y) pp78
    (fun y a b c => (bet78 y a b c).2) H8
  have H6 := chain_step (P := fun y => (HashPol.avoid 0).NodeOK code y) e7
    (nokAt x6 cB6 .call hx6 hat6) H7
  have H5 := chain_trans (P := fun y => (HashPol.avoid 0).NodeOK code y) pp56
    (fun y a b c => (bet56 y a b c).2) H6
  have H4 := chain_step (P := fun y => (HashPol.avoid 0).NodeOK code y) e5
    (nokAt x4 cB4 .call hx4 hat4) H5
  have H3 := chain_trans (P := fun y => (HashPol.avoid 0).NodeOK code y) pp34
    (fun y a b c => (bet34 y a b c).2) H4
  have H2 := chain_step (P := fun y => (HashPol.avoid 0).NodeOK code y) e3
    (nokAt x2 cB2 .staticcall hx2 hat2) H3
  have H1 := chain_trans (P := fun y => (HashPol.avoid 0).NodeOK code y) pp12
    (fun y a b c => (bet12 y a b c).2) H2
  have H0 := chain_trans (P := fun y => (HashPol.avoid 0).NodeOK code y) pp01
    (fun y a b c => (bet01 y a b c).2) H1
  -- no release `SSTORE` between the body start and the ETH `CALL`
  have h2' : okNoRel x2.pc = true := by rw [hx2.1, pB2]; decide
  have hPr : ∀ y, ParentPrefix x1 y → ParentPrefix y x4 → y ≠ x4 → y.pc ∉ lockReleasePcs := by
    intro y a b c
    have := interval_trans (P := fun y => okNoRel y.pc = true) pp12
      (fun y a b c => (bet12 y a b c).1) h2'
      (interval_step e3 h2' (fun y a b c => (bet34 y a b c).1)) y a b c
    simpa only [okNoRel, List.contains_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] using this
  exact ⟨exF, halt1_childAgree codeTries hag8 wB9, x1, x4, t1, xr, q, G, t2, pp01,
    hx1.1.trans pB1, pp12.trans ((ParentPrefix.step e3 (.refl _)).trans pp34), hx4.1.trans pB4,
    (by rw [hx4.2.1, hx4.1]; exact hat4), hPr,
    sp2, nodeAt_re ht1, nodeAt_re hxr, hq, hG, nodeAt_re ht2, dsF, dsr, dsq, hre, H0⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
