import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Kernel

/-!
V- witness, frame 1 whole: `remove_liquidity(200, [0, 0], A)` on the deployed 0x6326
certificate, from `c0` to its `RETURN`, as a gas-exact run of the certificate's program,
conditional on exactly the obligations of its attacker child at step 339 (`callRun_cont`'s
premises, packaged as `ChildOk` and `ChildAgree`: a settled machine obtained from an
`Exec` of the machine its `CALL` spawns, with the EELS gas and output and its world
shadows).  The token's `transfer` at step 574 is run by the token's lifted certificate
and discharged here (`childOk_of_childRun`); the attacker frame's theorem discharges
the attacker child.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed

theorem fs1_zero : fs1[0]? = some t_0000_c0 := by kernel_rfl

/-- **Frame 1 of the V- witness.**  Given the attacker child `d1` (its `Exec` derivation
and settlement, `ChildOk`; its observed gas, output and success; its world shadows,
`ChildAgree`), frame 1, with the token child run by its own certificate, is a gas-exact
run of the certificate from `pre1` to a halted machine with the EELS gas and return data
`[100, 100]`, whose world has `totalSupply = 1800 < 1906 = balanceOf[A]` and the
remove-lock released, with no error. -/
theorem frame1_full (d1 : Devm)
    (g1 : d1.gasLeft = gasA) (o1 : d1.output = []) (e1 : d1.error = none)
    (k1 : ChildOk sevm1 cfg339 d1) (a1 : ChildAgree d1 keysA adrsA storA acsA) :
    ∃ post, SProg.RunExact fs1 sevm1 pre1 post ∧ post.gasLeft = 29372882 ∧
      post.output = word 100 ++ word 100 ∧
      (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧ post.error = none := by
  have hk := frame1_kernel d1
  rw [childObs_eq g1 o1 e1] at hk
  unfold run1 at hk
  split at hk
  · rename_i c1 h1
    have hc1 : cfg339 = c1 := by unfold cfg339; rw [h1]
    rw [hc1] at k1
    split at hk
    · rename_i c2 h2
      split at hk
      · rename_i c3 h3
        have s3 := ((wrun_cont h1).trans (callResume_cont h2 k1 a1)).trans (wrun_cont h3)
        split at hk
        · rename_i d2 cl hc
          split at hk
          · rename_i c4 h4
            obtain ⟨k2, a2⟩ := childOk_of_childRun
              (fun hcode hfork hrun => lift_exact Token.cert_check Token.cert_jumpsOk hcode hfork hrun)
              (s3.1 c0_agree) hc (callResume_error h4)
            have s := s3.trans (callResume_cont h4 k2 a2)
            generalize hr : wrun fs1 sevm1 188 c4 = r at hk
            rcases r with c | ⟨post | post, cl⟩ | _
            · simp [obs1, obs1EELS] at hk
            · simp only [obs1, obs1EELS, Option.some.injEq, Prod.mk.injEq] at hk
              obtain ⟨hg, ho, h26, hA, h2', he⟩ := hk
              obtain ⟨run, hcl, hst⟩ := wrun_done hr (s.1 c0_agree)
              have hs : ∀ a k, storOf post.state a k = lookupS cl.stor a k := fun a k => by
                rw [hst post rfl]; exact hcl.2.2.1 a k
              refine ⟨post, ⟨t_0000_c0, fs1_zero, s.2 _ c0_agree run⟩, hg, ?_, ?_, ?_, ?_, ?_⟩
              · exact List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho
              · rw [hs]; exact h26
              · rw [hs]; exact hA
              · rw [hs]; exact h2'
              · exact Option.isNone_iff_eq_none.mp he
            · simp [obs1, obs1EELS] at hk
            · simp [obs1, obs1EELS] at hk
          · simp [obs1, obs1EELS] at hk
        all_goals simp [obs1, obs1EELS] at hk
      · simp [obs1, obs1EELS] at hk
    · simp [obs1, obs1EELS] at hk
  · simp [obs1, obs1EELS] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
