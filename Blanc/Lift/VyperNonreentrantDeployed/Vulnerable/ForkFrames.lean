import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.ForkKernel

/-!
V- witness under every covered fork: the frames.

The frame lemmas of the message-level witness (`Frame1Full`, `Frame4Child`, `Frame3`,
`Frame2`) are restated for the machines the same run has under any covered fork `g`
(Prague, Osaka, BPO1, BPO2): each machine is the Prague machine with only its fork changed
(`withFork`).  The kernel facts are not re-evaluated: the certificate interpreter, the child
machinery and Jaune's driver are unchanged by the fork (`Blanc/Lift/NodeWalkFork.lean`,
`Blanc/Lift/WitnessFork.lean`), so every Prague kernel fact rewrites into the fact for `g`.
The run never executes `CLZ` (an invalid opcode at Prague), reads no blob price (the block has
no excess blob gas), and none of its frames enters `MODEXP` or `P256VERIFY`
(`ForkKernel.lean`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
  Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

attribute [local irreducible] cfg339 e2 cc2 aCall cp3 e3 cp4 e4 post4

variable {g : Fork}

/-! ### The block environment every frame inherits -/

theorem e2_stat : e2.sta.benvStat = sevm1.benvStat := childStart_stat start2_eq

theorem e3_stat : e3.sta.benvStat = e2.sta.benvStat :=
  (frameEnterS_stat e3_eq).trans (callPrep_stat cp3_eq).2

theorem e4_stat : e4.sta.benvStat = e3.sta.benvStat :=
  (frameEnterS_stat e4_eq).trans (dcallPrep_stat cp4_eq).2

theorem e2_block : e2.sta.benvStat.fork = .prague ∧ e2.sta.benvStat.excessBlobGas = 0 := by
  rw [e2_stat]; exact ⟨rfl, rfl⟩

theorem e3_block : e3.sta.benvStat.fork = .prague ∧ e3.sta.benvStat.excessBlobGas = 0 := by
  rw [e3_stat]; exact e2_block

theorem e4_block : e4.sta.benvStat.fork = .prague ∧ e4.sta.benvStat.excessBlobGas = 0 := by
  rw [e4_stat]; exact e3_block

theorem cp3_neutral : cp3.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.2.1) spawned_codeAddresses) (by decide)
    (by decide)

theorem cp4_neutral : cp4.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.2.2) spawned_codeAddresses) (by decide)
    (by decide)

/-! ### The machines each frame enters with, under `g` -/

theorem cfg339_at (hg : CoveredFork g) : wrun fs1 (sevm1.withFork g) 339 c0 = .cont cfg339 :=
  (wrun_withFork CoveredFork.prague hg rfl fs1 339 c0).trans cfg339_eq

theorem start2_at (hg : CoveredFork g) :
    childStart (sevm1.withFork g) cfg339 Attacker.t_0000_c0 = some (e2.withFork g, cc2) := by
  rw [childStart_withFork CoveredFork.prague hg, start2_eq]; rfl

theorem aCall_at (hg : CoveredFork g) : wrun fs2 (e2.withFork g).sta 24 cc2 = .cont aCall :=
  (wrun_withFork (by rw [e2_block.1]; exact CoveredFork.prague) hg e2_block.2 fs2 24 cc2).trans
    aCall_eq

theorem cp3_at (hg : CoveredFork g) :
    callPrep (e2.withFork g).sta aCall = some (cp3.withFork g) := by
  show callPrep (e2.sta.withFork g) aCall = _
  rw [callPrep_withFork (by rw [e2_block.1]; exact CoveredFork.prague) hg, cp3_eq]; rfl

theorem e3_at (hg : CoveredFork g) :
    frameEnterS (cp3.withFork g).f aCall.acs = .run (e3.withFork g) := by
  show frameEnterS (cp3.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (by rw [e2_block.1]; exact CoveredFork.prague) hg
    (callPrep_stat cp3_eq) cp3_neutral, e3_eq]
  rfl

theorem prefix3_at (hg : CoveredFork g) : stepN 11 (e3.withFork g) = some (e31.withFork g) :=
  stepN_withFork hg e3_block.1 e3_block.2 prefix3

theorem cp4_at (hg : CoveredFork g) :
    dcallPrep (e31.withFork g).sta e31.dyna adrs3 acs3 = some (cp4.withFork g) := by
  have hf : CoveredFork e31.sta.benvStat.fork := by
    show CoveredFork e3.sta.benvStat.fork
    rw [e3_block.1]; exact CoveredFork.prague
  have h := dcallPrep_withFork hf hg e31.dyna adrs3 acs3
  show dcallPrep (e31.sta.withFork g) e31.dyna adrs3 acs3 = _
  rw [h, cp4_eq]; rfl

theorem e4_at (hg : CoveredFork g) :
    frameEnterS (cp4.withFork g).f acs3 = .run (e4.withFork g) := by
  show frameEnterS (cp4.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (s := e3.sta) (by rw [e3_block.1]; exact CoveredFork.prague) hg
    (dcallPrep_stat cp4_eq) cp4_neutral, e4_eq]
  rfl

theorem r4_at (hg : CoveredFork g) : wrun fs1 (e4.withFork g).sta 4505 c4 = r4 :=
  wrun_withFork (by rw [e4_block.1]; exact CoveredFork.prague) hg e4_block.2 fs1 4505 c4

/-! ### The spawns -/

theorem cp3_spec_at (hg : CoveredFork g) :
    Xinst.step (e2.withFork g).sta aCall.devm .call =
        .spawn (cp3.withFork g).f (.call cp3.p cp3.oi cp3.os) ∧
      (∀ a, a ∈ cp3.p.accessedAddresses ↔ a ∈ cp3.adrs) ∧
      cp3.p.accessedStorageKeys = aCall.devm.accessedStorageKeys ∧
      (cp3.withFork g).f.isCreate = false ∧
      (cp3.withFork g).f.inner.accessedAddresses = cp3.p.accessedAddresses ∧
      (cp3.withFork g).f.inner.accessedStorageKeys = cp3.p.accessedStorageKeys ∧
      (cp3.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp3.withFork g).f.inner.benv.state = aCall.devm.state :=
  callPrep_spec (cp3_at hg) agree_aCall.2.1 agree_aCall.2.2.2

theorem cp4_spec_at (hg : CoveredFork g) :
    Xinst.step (e31.withFork g).sta e31.dyna .delegatecall =
        .spawn (cp4.withFork g).f (.call cp4.p cp4.oi cp4.os) ∧
      (∀ a, a ∈ cp4.p.accessedAddresses ↔ a ∈ cp4.adrs) ∧
      cp4.p.accessedStorageKeys = e31.dyna.accessedStorageKeys ∧
      (cp4.withFork g).f.isCreate = false ∧
      (cp4.withFork g).f.inner.accessedAddresses = cp4.p.accessedAddresses ∧
      (cp4.withFork g).f.inner.accessedStorageKeys = cp4.p.accessedStorageKeys ∧
      (cp4.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp4.withFork g).f.inner.benv.state = e31.dyna.state ∧ cp4.p.state = e31.dyna.state :=
  dcallPrep_spec (cp4_at hg) (fun a => by rw [e31_acc]; exact e3_adrs a)
    (by rw [e31_state]; exact e3_world.2)

/-! ### Frame 4 as the proxy's child -/

/-- **Frame 4 as the proxy's child, under any covered fork.** -/
theorem frame4_child_at (hg : CoveredFork g) :
    Nonempty (Exec (e4.withFork g).pc (e4.withFork g).sta (e4.withFork g).dyna (.ok post4)) ∧
      (cp4.withFork g).f.settle (.ok post4) = .ok post4 ∧
      ChildAgree post4 keys4 adrs4 storA acsA := by
  obtain ⟨hrun, -, -, herr, hk, ha, hs, hc⟩ := r4_facts
  obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := cp4_spec_at hg
  have h := frame_of_wrun (fs := fs1) (f := (cp4.withFork g).f) (acs := acs3)
    (keys := aCall.keys) (adrs := cp4.adrs) (stor := aCall.stor) (n := 4505)
    (cevm := e4.withFork g) (e4_at hg)
    (fun x => by rw [hik, hpk, e31_keys]; exact e3_keys x)
    (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e31_state]; exact e3_world.1 a k)
    (by rw [hst, e31_state]; exact e3_world.2) hcr hsg
    (fun hr => lift_exactM cert_checkM cert_jumpsOkM e4_code (hg : CoveredFork g) hr) fs1_zero
    ⟨id, fun _ _ r => r⟩ ((r4_at hg).trans hrun) herr
  rw [hk, ha, hs, hc] at h
  exact h

/-! ### The proxy frame (frame 3) as the attacker's child -/

/-- **Frame 3 (the proxy) as the attacker's child, under any covered fork.** -/
theorem frame3_child_at (hg : CoveredFork g) :
    ChildOk (e2.withFork g).sta aCall post3 ∧ ChildAgree post3 keys3 adrs3' storA acsA ∧
      post3.gasLeft = gas3 ∧ post3.output = word 106 ∧ post3.error = none := by
  obtain ⟨hx4, hs4, ha4⟩ := frame4_child_at hg
  obtain ⟨hstep4, hpa, hpk, -, -, -, -, hst4, -⟩ := cp4_spec_at hg
  obtain ⟨-, -, -, hcr3, -, -, hsg3, -⟩ := cp3_spec_at hg
  have hr := resume3_eq post4
  have ht := tail3_eq post4
  have hh := return3_eq post4
  have ho := post3_obs post4
  have hk := post3_keep post4
  rw [obsChild4_post4] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hgas, hout, he⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : post3.error = none := Option.isNone_iff_eq_none.mp he
  -- the proxy frame's `Exec`
  have hspawn : Evm.step (e31.withFork g) =
      .spawn (cp4.withFork g).f (.call cp4.p cp4.oi cp4.os) 32 := by
    have hat : Ninst.At (e31.withFork g).sta.code 31 (.exec .delegatecall) := by
      show Ninst.At e3.sta.code 31 (.exec .delegatecall)
      rw [e3_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, (e31.withFork g).sta, e31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep4]
    rfl
  have henter : (cp4.withFork g).f.enter = .run (e4.withFork g) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst4]; exact e3_world.2)]; exact e4_at hg
  have hsettle : Resume.run (.call cp4.p cp4.oi cp4.os) ((cp4.withFork g).f.settle (.ok post4)) =
      .ok (d32 post4) := by
    rw [hs4]; exact resumeCallB_sound hr
  have hsta : (e44 post4).sta = e3.sta := stepN_sta (evm := ⟨32, e3.sta, d32 post4⟩) ht
  have hstep_halt : Evm.step ((e44 post4).withFork g) = .halt (.ok (post3F post4)) := by
    have hp : (e44 post4).sta.benvStat.fork = .prague := by rw [hsta]; exact e3_block.1
    have hx : (e44 post4).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact e3_block.2
    rw [show Evm.step ((e44 post4).withFork g) = (Evm.step (e44 post4)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx3 : Nonempty (Exec (e3.withFork g).pc (e3.withFork g).sta (e3.withFork g).dyna
      (.ok post3)) :=
    exec_of_stepN_spawn_runOk (prefix3_at hg) hspawn henter hx4 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, e3.sta, d32 post4⟩) e3_block.1
        e3_block.2 ht) hstep_halt)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post4.error.isSome = false := by rw [r4_facts.2.2.2.1]; rfl
  refine ⟨fun cp cevm hp he' => ?_, ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩,
    hgas, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr⟩
  · rw [cp3_at hg] at hp; cases hp
    rw [e3_at hg] at he'; cases he'
    exact ⟨.ok post3, hx3, frame_settle_ok hcr3 hsg3 herr⟩
  · show a ∈ post3.accessedAddresses ↔ _
    rw [show post3 = post3F post4 from rfl, hka, (hacc.1 a), hpe, hpa a, ha4.1 a]
    simp only [true_and, adrs3', List.mem_append]
  · show x ∈ post3.accessedStorageKeys ↔ _
    rw [show post3 = post3F post4 from rfl, hkk, (hacc.2 x), hpe, hpk, ha4.2.1 x]
    simp only [true_and, keys3, List.mem_append]
    rw [show e31.dyna.accessedStorageKeys = e3.dyna.accessedStorageKeys from rfl, e3_keys x]
  · show storOf post3.state a k = _
    rw [show post3 = post3F post4 from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.1 a k
  · show acctView (post3.state.get a) = _
    rw [show post3 = post3F post4 from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.2 a

/-! ### The attacker frame (frame 2) as frame 1's child -/

/-- **The attacker frame as frame 1's child, under any covered fork.** -/
theorem attacker_of_child_at (hg : CoveredFork g) (d3 : Devm)
    (k3 : ChildOk (e2.withFork g).sta aCall d3)
    (a3 : ChildAgree d3 keys3 adrs3' storA acsA) (g3 : d3.gasLeft = gas3)
    (o3 : d3.output = word 106) (e3' : d3.error = none) :
    ChildOk (sevm1.withFork g) cfg339 (haltedOf (run2 d3)) ∧
      ChildAgree (haltedOf (run2 d3)) keysA adrsA storA acsA ∧
      (haltedOf (run2 d3)).gasLeft = gasA ∧ (haltedOf (run2 d3)).output = [] ∧
      (haltedOf (run2 d3)).error = none := by
  have hk := frame2_kernel d3
  rw [show obsChild3 d3 = d3 from childObs_eq g3 o3 e3'] at hk
  have hf2 : CoveredFork e2.sta.benvStat.fork := by rw [e2_block.1]; exact CoveredFork.prague
  unfold run2 at hk ⊢
  split at hk
  · rename_i c hc
    have hcg : callResume (e2.withFork g).sta aCall d3 keys3 adrs3' storA acsA = some c :=
      (callResume_withFork hf2 hg _ _ _ _ _ _).trans hc
    generalize hr : wrun fs2 e2.sta 2 c = r at hk ⊢
    rcases r with c' | ⟨d | d, cl⟩ | _
    · simp only [obs2, reduceCtorEq] at hk
    · simp only [obs2, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hgas, ho, ⟨⟨⟨he, hkk⟩, hka⟩, hks⟩, hkc⟩ := hk
      have herr : d.error = none := Option.isNone_iff_eq_none.mp he
      have hstep := (wrun_cont (aCall_at hg)).trans (callResume_cont hcg k3 a3)
      have hrg : wrun fs2 (e2.withFork g).sta 2 c = .done (.halted d) cl :=
        (wrun_withFork hf2 hg e2_block.2 fs2 2 c).trans hr
      obtain ⟨hok, hag⟩ := childOk_of_start
        (fun hcode hfork hr' => lift_exact Attacker.cert_check Attacker.cert_jumpsOk hcode hfork hr')
        agree_cfg339 fs2_zero (start2_at hg) (hg : CoveredFork g) e2_code hstep hrg herr
      rw [hkk, hka, hks, hkc] at hag
      exact ⟨hok, hag, hgas, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
        herr⟩
    · simp only [obs2, reduceCtorEq] at hk
    · simp only [obs2, reduceCtorEq] at hk
  · simp only [obs2, reduceCtorEq] at hk

/-- **The attacker's subtree as frame 1's child, under any covered fork.** -/
theorem attacker_child_at (hg : CoveredFork g) :
    ChildOk (sevm1.withFork g) cfg339 post2 ∧ ChildAgree post2 keysA adrsA storA acsA ∧
      post2.gasLeft = gasA ∧ post2.output = [] ∧ post2.error = none :=
  let ⟨k3, a3, g3, o3, e3'⟩ := frame3_child_at hg
  attacker_of_child_at hg post3 k3 a3 g3 o3 e3'

/-! ### Frame 1 -/

/-- **Frame 1 of the V- witness under any covered fork** (`Frame1Full.frame1_full`): given the
attacker child `d1`, frame 1, with the token child run by its own certificate, is a gas-exact
run of the certificate from `pre1`. -/
theorem frame1_full_at (hg : CoveredFork g) (d1 : Devm)
    (g1 : d1.gasLeft = gasA) (o1 : d1.output = []) (e1 : d1.error = none)
    (k1 : ChildOk (sevm1.withFork g) cfg339 d1) (a1 : ChildAgree d1 keysA adrsA storA acsA) :
    ∃ post, SProg.RunExact fs1 (sevm1.withFork g) pre1 post ∧ post.gasLeft = 29372882 ∧
      post.output = word 100 ++ word 100 ∧
      (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧ post.error = none := by
  have hk := frame1_kernel d1
  rw [childObs_eq g1 o1 e1] at hk
  have hk' : obs1 (callPairFrom fs1 (sevm1.withFork g) fsT Token.code 234 23 188 keysA adrsA
      storA acsA (wrun fs1 (sevm1.withFork g) 339 c0) d1) = obs1EELS := by
    rw [callPairFrom_withFork CoveredFork.prague hg rfl, wrun_withFork CoveredFork.prague hg rfl]
    exact hk
  clear hk
  unfold callPairFrom at hk'
  split at hk'
  · rename_i c1 h1
    have hc1 : cfg339 = c1 := by
      have h1' : wrun fs1 sevm1 339 c0 = .cont c1 :=
        (wrun_withFork CoveredFork.prague hg rfl fs1 339 c0).symm.trans h1
      unfold cfg339; rw [h1']
    rw [hc1] at k1
    split at hk'
    · rename_i c2 h2
      split at hk'
      · rename_i c3 h3
        have s3 := ((wrun_cont h1).trans (callResume_cont h2 k1 a1)).trans (wrun_cont h3)
        split at hk'
        · rename_i d2 cl hc
          split at hk'
          · rename_i c4 h4
            obtain ⟨k2, a2⟩ := childOk_of_childRun
              (fun hcode hfork hrun => lift_exact Token.cert_check Token.cert_jumpsOk hcode hfork hrun)
              (s3.1 c0_agree) hc (callResume_error h4)
            have s := s3.trans (callResume_cont h4 k2 a2)
            generalize hr : wrun fs1 (sevm1.withFork g) 188 c4 = r at hk'
            rcases r with c | ⟨post | post, cl⟩ | _
            · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
            · simp only [obs1, obs1EELS, Option.some.injEq, Prod.mk.injEq] at hk'
              obtain ⟨hgas, ho, h26, hA, h2', he⟩ := hk'
              obtain ⟨run, hcl, hst⟩ := wrun_done hr (s.1 c0_agree)
              have hs : ∀ a k, storOf post.state a k = lookupS cl.stor a k := fun a k => by
                rw [hst post rfl]; exact hcl.2.2.1 a k
              refine ⟨post, ⟨t_0000_c0, fs1_zero, s.2 _ c0_agree run⟩, hgas, ?_, ?_, ?_, ?_, ?_⟩
              · exact List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho
              · rw [hs]; exact h26
              · rw [hs]; exact hA
              · rw [hs]; exact h2'
              · exact Option.isNone_iff_eq_none.mp he
            · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
            · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
          · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
        all_goals simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
      · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
    · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'
  · simp only [obs1, obs1EELS, List.map_append, reduceCtorEq] at hk'

/-- **Frame 1 of the V- witness, closed, under any covered fork** (`frame1_closed`). -/
theorem frame1_closed_at (hg : CoveredFork g) :
    ∃ post, SProg.RunExact fs1 (sevm1.withFork g) pre1 post ∧ post.gasLeft = 29372882 ∧
      post.output = word 100 ++ word 100 ∧
      (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧ post.error = none :=
  let ⟨k, a, g', o, e⟩ := attacker_child_at hg
  frame1_full_at hg post2 g' o e k a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
