import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Main

/-! # V+ capstone: from deployment to a blocked guarded reentry inside a committing operation

`vplus_reachable_capstone`, on every covered fork: from the disclosed `initialWorld` (only the
funded, code-free creator), nine messages, each from exactly the previous settled world:

1. the preserved implementation creation input (V1); 2. the synthetic clone creation (V1);
3. `initialize` through the clone; 4. `set_oracle(0, 0)` (V2, `CleanPool`);
5. the synthetic token CREATE (minting the creator's 10^6); 6. the labelled receiver CREATE;
7. `T.approve(P, 1000)`; 8. `P.add_liquidity([1000, 1000], 0)` with 1000 wei (V3);
9. `P.remove_liquidity(200, [0, 0], R)` (V5).

Immediately before message 9 the reached world is the `Checkpoint`, with the sound LP ledger
`totalSupply = Σ_{h ∈ {creator}} balanceOf[h]` (2000).  Message 9 succeeds; in its execution the
pool frame holds the lock (`ActiveRel`) when it pays `R`, `R` really attempts the guarded
`add_liquidity` through the clone, that frame is refused at the lock check and reverts, and
`vplus_exclusion` (instantiated, premises discharged) gives `¬ lockL.Enters P G`; the outer
call commits: `R` receives 100 wei and 100 `T`, the supply and the creator's LP balance fall to
1800 (the ledger stays sound: 1800 = 1800).  Message-level only; synthetic fixtures disclosed in
`Fund/World.lean`. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Jaune.Exec.Deriv (ParentPrefix)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel lockBodies lockL)

theorem world8_eq : world8 = dD.state := by unfold world8; rfl

/-- **The V+ reachable capstone.**  See the module docstring. -/
theorem vplus_reachable_capstone (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postInit postOracle postT postR postA postD postX : Devm,
      -- messages 1–8, each from the previous settled world
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postInit ∧ postInit.error = none ∧
      processMessage (oracleMsg fork postInit.state) = .ok postOracle ∧
      postOracle.error = none ∧ CleanPool postOracle.state ∧
      processCreateMessage (tokenCreateMsg fork postOracle.state) = .ok postT ∧
      postT.error = none ∧
      processCreateMessage (receiverCreateMsg fork postT.state) = .ok postR ∧
      postR.error = none ∧
      processMessage (approveMsg fork postR.state) = .ok postA ∧ postA.error = none ∧
      processMessage (addMsg fork postA.state) = .ok postD ∧ postD.error = none ∧
      -- the sound ledger immediately before the outer call
      Checkpoint postD.state ∧
      (storOf postD.state proxyAddr 0x16).toNat =
        Blanc.ledgerSumOn {creator} (fun holder => storOf postD.state proxyAddr (lpSlot holder)) ∧
      storOf postD.state proxyAddr 0x16 = 2000 ∧
      -- message 9: the outer call succeeds, from the checkpoint
      processMessage (removeMsg fork postD.state) = .ok postX ∧ postX.error = none ∧
      postX.gasLeft = 920078 ∧
      (Frame.ofCall (removeMsg fork postD.state)).enter = .run (eTop.re fork world8) ∧
      postD.state = world8 ∧ postX = dTop ∧
      ∃ (out : Execution) (R : Exec 0 (reS eTop.sta fork) eTop.dyna out)
        (F h c q G : Exec.Deriv),
        -- lock acquisition and the ETH payment to the receiver
        F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧ h.pc = 7427 ∧
        c.sevm.currentTarget = receiverAddr ∧ c.sevm.value.toNat = 100 ∧
        -- the attempted guarded entry, refused at the lock
        q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddr ∧
        G ∈ Exec.rawFrameRoots q.exc ∧ CPFrame proxyAddr code G ∧ G.sevm.data = reentryData ∧
        G.exn = .error (.revert, dRe) ∧ (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
        (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧
        -- `vplus_exclusion`, instantiated for `R`
        lockL.HashAvoidIn proxyAddr R ∧ ¬ lockL.Enters proxyAddr G ∧
        -- settlement of the outer call
        out = .ok postX ∧
        (storOf postX.state proxyAddr 0x16).toNat =
          Blanc.ledgerSumOn {creator} (fun holder => storOf postX.state proxyAddr (lpSlot holder)) ∧
        storOf postX.state proxyAddr 0x16 = 1800 ∧
        (postX.state.get receiverAddr).bal = 100 ∧
        storOf postX.state tokenAddr receiverAddr.toB256 = 100 ∧
        (postX.state.get proxyAddr).bal = 900 ∧ storOf postX.state proxyAddr 0 = 3 := by
  obtain ⟨postI, postP, postInit, postOracle, postT, postR, postA, postD, h1, e1, h2, e2, h3, e3, -,
    h4, e4, -, hclean, h5, e5, -, h6, e6, -, h7, e7, -, h8, e8, -, -, hck, hD⟩ :=
    setup_funded fork hfork
  have hw8 : postD.state = world8 := by rw [hD, world8_eq]
  have hck8 : Checkpoint world8 := hw8 ▸ hck
  obtain ⟨hm, hdT, hgas, -, hWX, hent, -, out, R, F, h, c, q, G, -, -, -, -, hash, hF, act, sp,
    hpc, -, hct, -, hcv, hq, hqt, -, hGq, -, cpG, hdG, exG, nb, chk, excl, hout⟩ :=
    vplus_reach_exit fork hfork hck8
  obtain ⟨led, sup, -⟩ := checkpoint_facts hck
  obtain ⟨ledX, supX, -, lockX, balP, balR, tR, -, -⟩ := exit_world_facts hWX
  refine ⟨postI, postP, postInit, postOracle, postT, postR, postA, postD, dTop, h1, e1, h2, e2,
    h3, e3, h4, e4, hclean, h5, e5, h6, e6, h7, e7, h8, e8, hck, led, sup,
    by rw [hw8]; exact hm, hdT, hgas, by rw [hw8]; exact hent, hw8, rfl, out, R, F, h, c, q, G,
    hF, act, sp, hpc, hct, hcv, hq, hqt, hGq, cpG, hdG, exG, nb, chk, hash, excl, hout, ledX, supX,
    balR, tR, balP, lockX⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
