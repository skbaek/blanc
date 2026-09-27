import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Kernel

/-!
V- witness, frame 1 whole: `remove_liquidity(200, [0, 0], A)` on the deployed 0x6326
certificate, from `c0` to its `RETURN`, as a gas-exact run of the certificate's program,
conditional on exactly the obligations of its two code children (`callRun_cont`'s
premises, packaged as `ChildOk` and `ChildAgree`): the attacker's subtree at step 339
and the token's `transfer` at step 574, each a settled machine obtained from an `Exec`
of the machine its `CALL` spawns, with the EELS gas and output and the EELS world
shadows.  Later units discharge them (the attacker frame with its reentrant
`add_liquidity`, and the token frame).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed

theorem fs1_zero : fs1[0]? = some t_0000_c0 := by kernel_rfl

private theorem stepOk_trans {fs : List SFunc} {sevm : Sevm} {c c' c'' : Cfg}
    (s1 : StepOk fs sevm c c') (s2 : StepOk fs sevm c' c'') : StepOk fs sevm c c'' :=
  ⟨fun hc => s2.1 (s1.1 hc), fun o hc r => s1.2 o hc (s2.2 o (s1.1 hc) r)⟩

/-- **Frame 1 of the V- witness.**  Given the attacker child `d1` and the token child
`d2` (their `Exec` derivations and settlements, `ChildOk`; their observed gas, output
and success; their world shadows, `ChildAgree`), frame 1 is a gas-exact run of the
certificate from `pre1` to a halted machine with the EELS gas and return data
`[100, 100]`, whose world has `totalSupply = 1800 < 1906 = balanceOf[A]` and the
remove-lock released. -/
theorem frame1_full (d1 d2 : Devm)
    (g1 : d1.gasLeft = gasA) (o1 : d1.output = []) (e1 : d1.error = none)
    (k1 : ChildOk sevm1 cfg339 d1) (a1 : ChildAgree d1 keysA adrsA storA acsA)
    (g2 : d2.gasLeft = gasT) (o2 : d2.output = word 1) (e2 : d2.error = none)
    (k2 : ChildOk sevm1 (cfg574 d1) d2) (a2 : ChildAgree d2 keysT adrsT storT acsT) :
    ∃ post, SProg.RunExact fs1 sevm1 pre1 post ∧ post.gasLeft = 29372882 ∧
      post.output = word 100 ++ word 100 ∧
      (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post.state proxyAddress (2 : Nat).toB256).toNat = 0 := by
  have hk := frame1_kernel d1 d2
  rw [childObs_eq g1 o1 e1, childObs_eq g2 o2 e2] at hk
  unfold run1 at hk
  split at hk
  · rename_i c1 h1
    have hc1 : cfg339 = c1 := by unfold cfg339; rw [h1]
    split at hk
    · rename_i c2 h2
      split at hk
      · rename_i c3 h3
        have hc3 : cfg574 d1 = c3 := by unfold cfg574; rw [hc1, h2]; dsimp only; rw [h3]
        split at hk
        · rename_i c4 h4
          rw [hc1] at k1
          rw [hc3] at k2
          have s := stepOk_trans (stepOk_trans (stepOk_trans (wrun_cont h1)
            (callResume_cont h2 k1 a1)) (wrun_cont h3)) (callResume_cont h4 k2 a2)
          generalize hr : wrun fs1 sevm1 188 c4 = r at hk
          rcases r with c | ⟨post | post, cl⟩ | _
          · simp [obs1, obs1EELS] at hk
          · simp only [obs1, obs1EELS, Option.some.injEq, Prod.mk.injEq] at hk
            obtain ⟨hg, ho, h26, hA, h2'⟩ := hk
            obtain ⟨run, hcl, hst⟩ := wrun_done hr (s.1 c0_agree)
            have hs : ∀ a k, storOf post.state a k = lookupS cl.stor a k := fun a k => by
              rw [hst post rfl]; exact hcl.2.2.1 a k
            refine ⟨post, ⟨t_0000_c0, fs1_zero, s.2 _ c0_agree run⟩, hg, ?_, ?_, ?_, ?_⟩
            · exact List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho
            · rw [hs]; exact h26
            · rw [hs]; exact hA
            · rw [hs]; exact h2'
          · simp [obs1, obs1EELS] at hk
          · simp [obs1, obs1EELS] at hk
        · simp [obs1, obs1EELS] at hk
      · simp [obs1, obs1EELS] at hk
    · simp [obs1, obs1EELS] at hk
  · simp [obs1, obs1EELS] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
