import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.AddRun
import Blanc.Lift.NodeWalkFrames

/-!
# V+ message 8: the first `add_liquidity` succeeds, on every covered fork

The frames of `AddRun.lean`, for every derivation, under any covered fork and the real original
state `world7` (`walk_re`, `scallSpawn_re`, `callSpawn_re`): the token's `balanceOf` and
`transferFrom` frames are leaves; the pool body makes both calls and returns; the forwarder
root settles (`forwarder_root_re`).  No success, token reply or post-state is assumed.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

attribute [local irreducible] cD1 cpD eDB cDB1 cpBal eBal cBal1 dBal dDB2 cDB3 cpTf eTf cTf1 dTf
  dDB4 cDB5 dDB dD2 cD3 dD

/-- **The token's `balanceOf(P)` frame**: a leaf returning the word 0. -/
theorem frameBalD {g : Fork} (hg : CoveredFork g) (hs : ReOK world7 eBal.sta)
    (hag : PAgree cBal0) :
    ∀ t, NodeAt ((eBal.sta.withFork g).withOrig world7) cBal0 t → t.exn = .ok dBal ∧
      Exec.rawFrameDescendants t.exc = [] ∧
      ChildAgree dBal cBal1.keys cBal1.adrs cBal1.stor cBal1.acs := by
  intro t ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, w1, w2, -⟩ := addFacts
  have hcode : ((eBal.sta.withFork g).withOrig world7).code =
      Blanc.Lift.VyperNonreentrantDeployed.Token20.code :=
    (Prod.mk.inj (Prod.mk.inj hst).2).2
  have w1' := (walk_re hs hg (.avoid 0) tokenTries okAny 29 cBal0).trans w1
  have w2' := (walk_re hs hg (.avoid 0) tokenTries okAny 1 cBal1).trans w2
  obtain ⟨hca, hall⟩ := leaf_frame_ok (.avoid 0) tokenTries hcode okAny hag w1' w2'
  obtain ⟨ex, ds, -⟩ := hall t ht
  exact ⟨ex, ds, hca⟩

/-- **The token's `transferFrom(creator, P, 1000)` frame**: a leaf returning the word 1. -/
theorem frameTfD {g : Fork} (hg : CoveredFork g) (hs : ReOK world7 eTf.sta)
    (hag : PAgree cTf0) :
    ∀ t, NodeAt ((eTf.sta.withFork g).withOrig world7) cTf0 t → t.exn = .ok dTf ∧
      Exec.rawFrameDescendants t.exc = [] ∧
      ChildAgree dTf cTf1.keys cTf1.adrs cTf1.stor cTf1.acs := by
  intro t ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, w1,
    w2, -⟩ := addFacts
  have hcode : ((eTf.sta.withFork g).withOrig world7).code =
      Blanc.Lift.VyperNonreentrantDeployed.Token20.code :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hst).2).2).1
  have w1' := (walk_re hs hg (.avoid 0) tokenTries okAny 85 cTf0).trans w1
  have w2' := (walk_re hs hg (.avoid 0) tokenTries okAny 1 cTf1).trans w2
  obtain ⟨hca, hall⟩ := leaf_frame_ok (.avoid 0) tokenTries hcode okAny hag w1' w2'
  obtain ⟨ex, ds, -⟩ := hall t ht
  exact ⟨ex, ds, hca⟩

/-- **The pool body of `add_liquidity`**, under any covered fork and the real original state:
it calls `T.balanceOf(P)` and `T.transferFrom(creator, P, 1000)`, mints and returns. -/
theorem frameDB {g : Fork} (hg : CoveredFork g) (hs : ReOK world7 eDB.sta) (hag : PAgree cDB0) :
    ∀ F, NodeAt ((eDB.sta.withFork g).withOrig world7) cDB0 F → F.exn = .ok dDB ∧
      ChildAgree dDB cDB5.keys cDB5.adrs cDB5.stor cDB5.acs := by
  intro F hF
  obtain ⟨-, -, -, -, -, -, -, hstB, -, wB1, pB1, dB1, scallBal, caBal, enterBal, -, -, -,
    balErr, resB2, wB3, pB3, dB3, callTf, caTf, enterTf, -, -, -, tfErr, resB4, wB5, wB6,
    -⟩ := addFacts
  have hcode : ((eDB.sta.withFork g).withOrig world7).code = code :=
    (Prod.mk.inj (Prod.mk.inj hstB).2).2
  have w1 := (walk_re hs hg (.avoid 0) codeTries okAny 121 cDB0).trans wB1
  have w3 := (walk_re hs hg (.avoid 0) codeTries okAny 1269 cDB2).trans wB3
  have w5 := (walk_re hs hg (.avoid 0) codeTries okAny 122 cDB4).trans wB5
  have w6 := (walk_re hs hg (.avoid 0) codeTries okAny 1 cDB5).trans wB6
  have hsBal : ReOK world7 eBal.sta :=
    ReOK.of_stat ((frameEnterS_stat enterBal).trans (scallPrep_stat scallBal).2) hs
  have hsTf : ReOK world7 eTf.sta :=
    ReOK.of_stat ((frameEnterS_stat enterTf).trans (callPrepP_stat callTf).2) hs
  obtain ⟨sBal, nBal⟩ := scallSpawn_re hs hg scallBal
    (Frame.precompNeutral_of_codeAddress caBal (by decide) (by decide)) enterBal
  obtain ⟨sTf, nTf⟩ := callSpawn_re hs hg callTf
    (Frame.precompNeutral_of_codeAddress caTf (by decide) (by decide)) enterTf
  -- the `STATICCALL` of `balanceOf`
  obtain ⟨hag1, h1⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 121 cDB0 cDB1 hag w1
  obtain ⟨x1, hx1, -, ex1, -, -⟩ := h1 F hF
  have hat1 : Ninst.At ((eDB.sta.withFork g).withOrig world7).code cDB1.pc (.exec .staticcall) := by
    rw [hcode, pB1]; exact decodeT_sound codeTries dB1
  obtain ⟨step1, ent1, -, hagBal⟩ := staticcall_node hag1 hat1 sBal nBal
  have hF1 := (scallPrep_node_facts hag1 sBal).2
  obtain ⟨t1, x2, -, -, e2, hx2, ex2, -, hag2⟩ :=
    spawn_resume_ok hx1 hag1 hF1 step1 ent1 balErr resB2
      (fun t ht => let r := frameBalD hg hsBal hagBal t ht; ⟨r.1, r.2.2⟩)
  -- the `CALL` of `transferFrom`
  obtain ⟨hag3, h3⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 1269 cDB2 cDB3 hag2 w3
  obtain ⟨x3, hx3, -, ex3, -, -⟩ := h3 x2 hx2
  have hat3 : Ninst.At ((eDB.sta.withFork g).withOrig world7).code cDB3.pc (.exec .call) := by
    rw [hcode, pB3]; exact decodeT_sound codeTries dB3
  obtain ⟨step3, ent3, -, hagTf, hF3⟩ := call_node hag3 hat3 sTf nTf
  obtain ⟨t2, x4, -, -, e4, hx4, ex4, -, hag4⟩ :=
    spawn_resume_ok hx3 hag3 hF3 step3 ent3 tfErr resB4
      (fun t ht => let r := frameTfD hg hsTf hagTf t ht; ⟨r.1, r.2.2⟩)
  -- the mint, and `RETURN`
  obtain ⟨hag5, h5⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 122 cDB4 cDB5 hag4 w5
  obtain ⟨x5, hx5, -, ex5, -, -⟩ := h5 x4 hx4
  obtain ⟨ex6, -, -⟩ := pwalkH_halt (.avoid 0) codeTries hcode okAny 1 cDB5 _ hag5 w6 x5 hx5
  exact ⟨by rw [← ex1, ← ex2, ← ex3, ← ex4, ← ex5]; exact ex6,
    halt1_childAgree codeTries hag5 w6⟩

/-- **Message 8, `add_liquidity([1000, 1000], 0)` with 1000 wei from the creator**, on every
covered fork, from the world `approve` settles to: it settles to the closed machine `dD` with
871,140 of its 1,000,000 gas left and a refund counter of 4,800; the world holds the account
views `acsAdd` (1000 wei moved from the creator to the clone) and exactly the storage `storAdd`
(supply 2000, the creator's 2000 liquidity tokens, the token's balances, the lock released). -/
theorem add_run (g : Fork) (hg : CoveredFork g) (hW : WorldIs world7 acs6 stor7) :
    processMessage (addMsg g world7) = .ok dD ∧ dD.error = none ∧ dD.gasLeft = 871140 ∧
      dD.refundCounter = 4800 ∧ WorldIs dD.state acsAdd storAdd := by
  obtain ⟨he, hst, w1, p1, d1, hp, heB, -, hca, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hdB, hr, w3, w4, hdT, hgas, hrc, hcanon, hkeys, -⟩ := addFacts
  have hO : OrigAgree world7 O7 := origAgree_origOf hW.2
  obtain ⟨hmsg, hca3⟩ := forwarder_root_re hg hW hO he hst w1 p1 d1 hp heB hca
    (fun hs hag => frameDB hg hs hag) hdB hr w3 w4 hdT
  refine ⟨hmsg, hdT, hgas, hrc, fun a => ?_, fun a k => ?_⟩
  · rw [hca3.2.2.2 a]; exact lookupA_eq_of_map hkeys a
  · rw [hca3.2.2.1 a k]; exact lookupS_eq_of_canonS hcanon a k

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
