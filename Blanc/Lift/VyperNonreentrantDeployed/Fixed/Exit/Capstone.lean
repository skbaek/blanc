import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Main
import Blanc.Lift.RootMessages

/-! # V+ capstone: from deployment to a blocked guarded reentry inside a committing operation

The public headline is `vplus_exit`: on every covered fork, eight setup messages from the
disclosed initial world reach a pool whose LP ledger is sound over its single holder
(`totalSupply = Σ_{h ∈ {creator}} balanceOf[h] = 2000`), and the exit `remove_liquidity(200, [0,
0], R)` then settles with the ledger still sound at 1800 and the receiver paid 100 wei, while the
receiver's guarded reentry during the exit is refused at the shared lock (`ReentryRefused`). It is
stated over the message fold `runMessages` and the storage observers `supply`/`lpBalance`. These
are **synthetic worlds** (synthetic clone, token and receiver code, supplied CREATE targets, a
creator-only start world): there is no live contract, so no deployment root applies.
`vplus_exclusion` instantiated for the exit's execution, with every frame rooted in the callback,
is in the detailed form `vplus_reachable_capstone` below.

The detailed form:

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
`vplus_exclusion` (instantiated, premises discharged) holds for every frame rooted in the callback's
execution, the witnessed reentry being one instance; the outer
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
        lockL.HashAvoidIn proxyAddr R ∧
        (∀ G' ∈ Exec.rawFrameRoots c.exc, ¬ lockL.Enters proxyAddr G') ∧
        ¬ lockL.Enters proxyAddr G ∧
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
    hpc, -, hct, -, hcv, hq, hqt, -, hGq, hGc, cpG, hdG, exG, nb, chk, excl, hout⟩ :=
    vplus_reach_exit fork hfork hck8
  obtain ⟨led, sup, -⟩ := checkpoint_facts hck
  obtain ⟨ledX, supX, -, lockX, balP, balR, tR, -, -⟩ := exit_world_facts hWX
  refine ⟨postI, postP, postInit, postOracle, postT, postR, postA, postD, dTop, h1, e1, h2, e2,
    h3, e3, h4, e4, hclean, h5, e5, h6, e6, h7, e7, h8, e8, hck, led, sup,
    by rw [hw8]; exact hm, hdT, hgas, by rw [hw8]; exact hent, hw8, rfl, out, R, F, h, c, q, G,
    hF, act, sp, hpc, hct, hcv, hq, hqt, hGq, cpG, hdG, exG, nb, chk, hash, excl, excl G hGc,
    hout, ledX, supX, balR, tR, balP, lockX⟩

/-! ### The headline: the exit over the message fold -/

/-- The pool's `totalSupply` word (storage slot `0x16` of the clone `proxyAddr`). -/
def supply (W : State) : B256 := storOf W proxyAddr 0x16

/-- The pool's `balanceOf[h]` word. -/
def lpBalance (W : State) (h : Adr) : B256 := storOf W proxyAddr (lpSlot h)

/-- The eight setup messages, all from the code-free `creator`: implementation and clone creation,
`initialize` and `set_oracle(0, 0)` through the clone, token and receiver creation, `approve`, and
`add_liquidity([1000, 1000], 0)` with 1000 wei. -/
def vplusSetup : List RootMsg :=
  [.create implCreateMsg, .create cloneCreateMsg, .call initMsg, .call oracleMsg,
    .create tokenCreateMsg, .create receiverCreateMsg, .call approveMsg, .call addMsg]

/-- The LP ledger is sound over its single holder `creator`, with supply `n`. -/
def LedgerSound (W : State) (n : B256) : Prop :=
  supply W = n ∧ (supply W).toNat = Blanc.ledgerSumOn {creator} (lpBalance W)

/-- **The fix refuses the reentry.** In the execution of the exit message from `W₀`, which
settles to `W`: the pool frame `F` holds the shared lock when it pays the receiver (frame `c`);
the receiver calls back into the pool through the clone, and the resulting pool frame `G`, running
the implementation's code with the guarded `add_liquidity` call `reentryData`, reverts without
entering any lock-guarded body (`¬ lockL.Enters`). -/
def ReentryRefused (fork : Fork) (W₀ W : State) : Prop :=
  ∃ (e : Evm) (out : Execution) (R : Exec 0 e.sta e.dyna out) (F h c q G : Exec.Deriv),
    (Frame.ofCall (removeMsg fork W₀)).enter = .run e ∧ (∃ d, out = .ok d ∧ d.state = W) ∧
    -- the pool frame holds the lock when it pays the receiver
    F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧
    c.sevm.currentTarget = receiverAddr ∧
    -- the receiver's guarded call back into the pool is refused at the lock
    q ∈ Exec.rawFrameRoots c.exc ∧ G ∈ Exec.rawFrameRoots q.exc ∧ CPFrame proxyAddr code G ∧
    G.sevm.data = reentryData ∧ (∃ d, G.exn = .error (.revert, d)) ∧
    ¬ lockL.Enters proxyAddr G

/-- **V+: the fixed pool refuses the reentry and its exit keeps the LP ledger sound.** On every covered fork, the setup
messages run from the disclosed `initialWorld` to a world `W₀` whose ledger is sound at 2000, and
the exit `removeMsg` (`remove_liquidity(200, [0, 0], receiverAddr)`, whose 100 wei payment lets
the receiver attempt a guarded re-entry, refused at the shared lock) then settles to a world `W`
whose ledger is sound at 1800, with the receiver paid 100 wei and its reentry refused
(`ReentryRefused`). Synthetic worlds: no live contract, so no deployment root; the instantiated
`vplus_exclusion` is in `vplus_reachable_capstone`. -/
theorem vplus_exit (fork : Fork) (hfork : CoveredFork fork) :
    ∃ W₀ W, runMessages fork initialWorld vplusSetup = some W₀ ∧ LedgerSound W₀ 2000 ∧
      runMessages fork W₀ [.call removeMsg] = some W ∧ LedgerSound W 1800 ∧
      (W.get receiverAddr).bal = 100 ∧ ReentryRefused fork W₀ W := by
  obtain ⟨postI, postP, postInit, postOracle, postT, postR, postA, postD, postX, h1, e1, h2, e2,
    h3, e3, h4, e4, -, h5, e5, h6, e6, h7, e7, h8, e8, -, led, sup, hm, hX, -, hent, -, -,
    out, R, F, h, c, q, G, hF, act, sp, -, hct, -, hq, -, hGq, cpG, hdG, exG, -, -, -, -, nE, hout,
    ledX, supX, balR, -⟩ := vplus_reachable_capstone fork hfork
  refine ⟨postD.state, postX.state, ?_, ⟨sup, led⟩, ?_, ⟨supX, ledX⟩, balR,
    ⟨eTop.re fork world8, out, R, F, h, c, q, G, hent, ⟨postX, hout, rfl⟩, hF, act, sp, hct, hq,
      hGq, cpG, hdG, ⟨dRe, exG⟩, nE⟩⟩
  · rw [vplusSetup, runMessages_cons_of_ok (m := .create implCreateMsg) h1 e1,
      runMessages_cons_of_ok (m := .create cloneCreateMsg) h2 e2,
      runMessages_cons_of_ok (m := .call initMsg) h3 e3,
      runMessages_cons_of_ok (m := .call oracleMsg) h4 e4,
      runMessages_cons_of_ok (m := .create tokenCreateMsg) h5 e5,
      runMessages_cons_of_ok (m := .create receiverCreateMsg) h6 e6,
      runMessages_cons_of_ok (m := .call approveMsg) h7 e7,
      runMessages_cons_of_ok (m := .call addMsg) h8 e8]
    rfl
  · rw [runMessages_cons_of_ok (m := .call removeMsg) hm hX]
    rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
