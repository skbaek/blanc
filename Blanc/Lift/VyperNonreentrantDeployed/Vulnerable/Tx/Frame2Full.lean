import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Kernel

/-!
V- as an admitted transaction, frame 2 whole as a child: `remove_liquidity(200, [0, 0], A')` on
the deployed 0x6326 certificate under the proxy's `DELEGATECALL`, from its start configuration
`c2T` to its `RETURN`, conditional on exactly the obligations of its callback child at step 339
(`callResume_cont`'s premises, packaged as `ChildOk` and `ChildAgree`).  The token's `transfer` at
step 574 is run by the token's lifted certificate and discharged here (`childOk_of_childRun`);
`Tx.Frame3` discharges the callback child.  The result is the frame the proxy's `DELEGATECALL`
spawns as an `Exec` of the real machine it enters with, settling to its halted machine, with the
shadows of its halting configuration and the corruption in its storage.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T

/-- Frame 2 runs the registered certificate's code: the fixture's implementation account holds
that very constant. -/
theorem e2T_code_fork : (e2T.sta.code, e2T.sta.benvStat.fork) = (code, .prague) := by kernel_rfl

theorem e2T_code : e2T.sta.code = code := (Prod.mk.inj e2T_code_fork).1

theorem e2T_fork : CoveredFork e2T.sta.benvStat.fork := by
  rw [(Prod.mk.inj e2T_code_fork).2]; exact CoveredFork.prague

/-- **Frame 2 of the V- tx witness, as the proxy's child.**  Given the callback child `d3` (its
`Exec` derivation and settlement, `ChildOk`; its observed gas, output and success; its world
shadows, `ChildAgree`), frame 2, with the token child run by its own certificate, is an `Exec`
of the real machine it enters with, settles to a halted machine with the EELS gas and return
data `[100, 100]` and no error, and the storage shadow of its halting configuration has
`totalSupply = 1800 < 1906 = balanceOf[A']` and the remove-lock released. -/
theorem frame2_child (d3 : Devm)
    (g3 : d3.gasLeft = gasAT) (o3 : d3.output = []) (e3' : d3.error = none)
    (r3 : d3.refundCounter = refund3) (t3 : d3.accountsToDelete = .emptyWithCapacity)
    (k3 : ChildOk e2T.sta cfg339T d3) (a3 : ChildAgree d3 keysAT adrsAT storAT acsAT) :
    ∃ (post : Devm) (cl : Cfg), Nonempty (Exec e2T.pc e2T.sta e2T.dyna (.ok post)) ∧
      cp2T.f.settle (.ok post) = .ok post ∧ ChildAgree post cl.keys cl.adrs cl.stor cl.acs ∧
      post.gasLeft = 28916293 ∧ post.output = word 100 ++ word 100 ∧ post.error = none ∧
      (lookupS cl.stor proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (lookupS cl.stor proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      (lookupS cl.stor proxyAddress (2 : Nat).toB256).toNat = 0 ∧
      post.refundCounter = refund2 ∧ post.accountsToDelete = .emptyWithCapacity := by
  have hk := frame2_kernel d3
  rw [childObsX_eq g3 o3 e3' r3 t3] at hk
  unfold run2T run2From callPairFrom at hk
  rw [← e2T_sta_eq] at hk
  split at hk
  · rename_i c1 h1
    have hc1 : cfg339T = c1 := by unfold cfg339T; rw [h1]
    rw [hc1] at k3
    split at hk
    · rename_i c2 h2
      split at hk
      · rename_i c3 h3
        have s3 := ((wrun_cont h1).trans (callResume_cont h2 k3 a3)).trans (wrun_cont h3)
        split at hk
        · rename_i d2 cl hc
          split at hk
          · rename_i c4 h4
            obtain ⟨k2, a2⟩ := childOk_of_childRun
              (fun hcode hfork hrun => lift_exact Token.cert_check Token.cert_jumpsOk hcode hfork hrun)
              (s3.1 c2T_agree) hc (callResume_error h4)
            have s := s3.trans (callResume_cont h4 k2 a2)
            generalize hr : wrun fs1 e2T.sta 188 c4 = r at hk
            rcases r with c | ⟨post | post, cl'⟩ | _
            · simp [obs2T, obs2TEELS] at hk
            · simp only [obs2T, obs2TEELS, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
                decide_eq_true_eq] at hk
              obtain ⟨hg, ho, h26, hA, h2', ⟨he, hrf⟩, hatd⟩ := hk
              obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := cp2T_spec
              have herr : post.error = none := Option.isNone_iff_eq_none.mp he
              obtain ⟨hx, hs, ha⟩ := frame_of_wrun (fs := fs1) (f := cp2T.f) (acs := acs1T)
                (keys := callCfg.keys) (adrs := cp2T.adrs) (stor := callCfg.stor) (n := 188)
                e2T_eq
                (fun x => by rw [hik, hpk, e1T31_keys]; exact e1T_keys x)
                (fun a => by rw [hia]; exact hpa a)
                (fun a k => by rw [hst, e1T31_state]; exact e1T_world.1 a k)
                (by rw [hst, e1T31_state]; exact e1T_world.2) hcr hsg
                (fun hr => lift_exactM cert_checkM cert_jumpsOkM e2T_code e2T_fork hr) fs1_zero
                s hr herr
              exact ⟨post, cl', hx, hs, ha, hg,
                List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho, herr, h26, hA, h2', hrf,
                hatd⟩
            · simp [obs2T, obs2TEELS] at hk
            · simp [obs2T, obs2TEELS] at hk
          · simp [obs2T, obs2TEELS] at hk
        all_goals simp [obs2T, obs2TEELS] at hk
      · simp [obs2T, obs2TEELS] at hk
    · simp [obs2T, obs2TEELS] at hk
  · simp [obs2T, obs2TEELS] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
