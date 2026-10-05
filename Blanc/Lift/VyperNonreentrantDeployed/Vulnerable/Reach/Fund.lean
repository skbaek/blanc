import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Init
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Deploy

/-! # V− setup, messages 4–5: executed creation of the token and the attacker

From exactly the world `setup_initialize` settles to (the clean, initialized pool), the
code-free `creator` executes two further root CREATE messages, each starting from the previous
settled world, on every covered fork:

* message 4 creates the shared token fixture `T` at `tokenAddr`; its constructor mints
  `balanceOf[creator] := 10^6` and installs the registered `Token20` runtime;
* message 5 creates the reachable attacker at `attackerAddr`; it installs the registered
  `AttackerR` runtime (the EOA-triggerable dispatcher repointed to `attackerAddr` and the new
  proxy).

`setup_funded` composes messages 1–5 and states the reached world `W4`: the token holds
`balanceOf[creator] = 10^6` with the token runtime, the attacker holds the attacker runtime,
the implementation keeps `fee = 31337`, the creator stays funded, and the proxy's storage is
still exactly the initializer's clean `initWrites` (the funding creations touch neither the
pool nor the implementation). This is the executed funding-contract step of V3; the `approve`
and first `add_liquidity` calls (which run node walks over a non-closed settled world, so need
the transaction-original-state agreement transport) continue from here. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun

/-- The token's balance slot of `creator` (the token's layout is `balSlot a = a`). -/
abbrev creatorBalSlot : B256 := creator.toB256

theorem tokenAddr_ne_proxyAddr : tokenAddr ≠ proxyAddr := by decide
theorem tokenAddr_ne_implAddr : tokenAddr ≠ implAddr := by decide
theorem tokenAddr_ne_creator : tokenAddr ≠ creator := by decide
theorem attackerAddr_ne_proxyAddr : attackerAddr ≠ proxyAddr := by decide
theorem attackerAddr_ne_implAddr : attackerAddr ≠ implAddr := by decide
theorem attackerAddr_ne_creator : attackerAddr ≠ creator := by decide
theorem attackerAddr_ne_tokenAddr : attackerAddr ≠ tokenAddr := by decide

/-- A CREATE that changes only `target`'s account preserves `storOf` elsewhere. -/
theorem storOf_of_create_ne {post : Devm} {W : State} {target : Adr}
    (h : ∀ a, a ≠ target → post.state.get a = W.get a) {b : Adr} (hb : b ≠ target) (k : B256) :
    storOf post.state b k = storOf W b k := by
  unfold storOf; rw [h b hb]

theorem acctView_of_create_ne {post : Devm} {W : State} {target : Adr}
    (h : ∀ a, a ≠ target → post.state.get a = W.get a) {b : Adr} (hb : b ≠ target) :
    acctView (post.state.get b) = acctView (W.get b) := by rw [h b hb]

/-- The token's original storage at `creator`'s slot, as the setup reaches it, is zero: the
funding world's `origState` is `postP.state` (fresh transaction), and the token is absent
there. This is what fixes message 4's `SSTORE` charge as cold-set (22,100). -/
theorem tokenOrig_zero (fork : Fork) (hfork : CoveredFork fork)
    {postP postC : Devm}
    (hrest : ∀ a, a ≠ proxyAddr → ∀ k, storOf postC.state a k = storOf postP.state a k)
    (hFP : ∀ a, a ≠ implAddr → a ≠ proxyAddr → postP.state.get a = initialWorld.get a) :
    storOf postC.state tokenAddr creatorBalSlot = 0 := by
  rw [hrest tokenAddr tokenAddr_ne_proxyAddr, storOf, hFP tokenAddr tokenAddr_ne_implAddr
    tokenAddr_ne_proxyAddr, initialWorld_get, if_neg tokenAddr_ne_creator]
  rfl

/-- **V− setup, messages 1–5, every covered fork.** The two creations execute from exactly the
initialized world, each from the previous settled world, with exact finite gas, and reach a
world in which the token is minted to the creator, the attacker is deployed, the pool is still
clean and the implementation keeps its sentinel. -/
theorem setup_funded (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postC tokenPost attackerPost : Devm,
      -- messages 1–3: creations and initialize (as in `setup_initialize`), each from the
      -- previous settled world
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      processMessage (initMsg fork postP.state) = .ok postC ∧
      CleanPool postC.state ∧
      -- message 4: token creation from the initialized world
      processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
      tokenPost.error = none ∧ tokenPost.gasLeft = 118019 ∧
      -- message 5: attacker creation from the token's settled world
      processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
      attackerPost.error = none ∧ attackerPost.gasLeft = 162748 ∧
      -- the reached world W4 = attackerPost.state
      storOf attackerPost.state tokenAddr creatorBalSlot = 1000000 ∧
      (attackerPost.state.get tokenAddr).code = Blanc.Lift.VyperNonreentrantDeployed.Token20.code ∧
      (attackerPost.state.get attackerAddr).code =
        Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.code ∧
      storOf attackerPost.state implAddr 10 = 31337 ∧
      (∀ k, storOf attackerPost.state proxyAddr k = lookupS initWrites proxyAddr k) ∧
      CleanPool attackerPost.state := by
  -- messages 1–3
  obtain ⟨postI, postP, postC, h1, _e1, _g1, h2, _e2, _g2, _hIa, _hPa, hFP, _hcode,
    _hp10, _hi10, h3, _e3, _g3, _o3, hPool, hrest, _hview, himpl, hclean⟩ :=
    setup_initialize fork hfork
  -- message 4: token creation over postC.state
  have hforkT : CoveredFork (tokenCreateMsg fork postC.state).benv.stat.fork := by
    show CoveredFork fork; exact hfork
  obtain ⟨tokenPost, hT, hTe, hTg, hTtok, hTrest, _hTstate⟩ :=
    Token20.Creation.create_token (tokenCreateMsg fork postC.state) hforkT rfl rfl rfl rfl rfl
      (by show (82000 : Nat) ≤ 200000; decide)
  -- fix message 4's gas: the token's original balance slot is zero (cold set 22,100)
  have hmint : Token20.Creation.mintSstoreGas (tokenCreateMsg fork postC.state) = 22100 := by
    have horig : (postC.state.get tokenAddr).stor.get creator.toB256 = 0 :=
      tokenOrig_zero fork hfork hrest hFP
    show (if (⟨tokenAddr, creator.toB256⟩ : Adr × B256) ∈
        (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) then 0 else gasColdSload)
        + sstoreValueCost ((postC.state.get tokenAddr).stor.get creator.toB256) 0 1000000 = 22100
    rw [horig, if_neg Std.HashSet.not_mem_emptyWithCapacity]; rfl
  have hTg' : tokenPost.gasLeft = 118019 := by
    rw [hTg, hmint]; show (200000 : Nat) - (81 + 22100) - 59800 = 118019; decide
  -- message 5: attacker creation over tokenPost.state
  have hforkA : CoveredFork (attackerCreateMsg fork tokenPost.state).benv.stat.fork := by
    show CoveredFork fork; exact hfork
  obtain ⟨attackerPost, hA, hAe, hAg, hAatk, hArest, _hAstate⟩ :=
    AttackerR.Creation.create_attacker (attackerCreateMsg fork tokenPost.state) hforkA rfl rfl rfl
      rfl (by show (37252 : Nat) ≤ 200000; decide)
  have hAg' : attackerPost.gasLeft = 162748 := by
    rw [hAg]; show (200000 : Nat) - 52 - 37200 = 162748; decide
  -- restate the creation results with the literal addresses
  have hTtok' : tokenPost.state.get tokenAddr = Token20.Creation.tokenAcct postC.state tokenAddr
      creator := hTtok
  have hAatk' : attackerPost.state.get attackerAddr =
      AttackerR.Creation.attackerAcct tokenPost.state attackerAddr := hAatk
  have hAT : attackerPost.state.get tokenAddr = tokenPost.state.get tokenAddr :=
    hArest tokenAddr (Ne.symm attackerAddr_ne_tokenAddr)
  -- the reached facts
  refine ⟨postI, postP, postC, tokenPost, attackerPost, h1, h2, h3, hclean, hT, hTe, hTg', hA, hAe,
    hAg', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- balanceOf[creator] = 10^6: set by message 4, preserved by message 5 (A ≠ T)
    rw [storOf, hAT, hTtok']
    show (Stor.empty.set creatorBalSlot 1000000).get creatorBalSlot = 1000000
    exact Stor.get_set_self _ _ _
  · -- token code, preserved by message 5
    rw [hAT, hTtok']; rfl
  · -- attacker code
    rw [hAatk']; rfl
  · -- implementation sentinel, preserved by both creations
    exact (storOf_of_create_ne hArest (Ne.symm attackerAddr_ne_implAddr) 10).trans
      ((storOf_of_create_ne hTrest (Ne.symm tokenAddr_ne_implAddr) 10).trans himpl)
  · -- proxy storage still the clean initWrites
    intro k
    exact (storOf_of_create_ne hArest (Ne.symm attackerAddr_ne_proxyAddr) k).trans
      ((storOf_of_create_ne hTrest (Ne.symm tokenAddr_ne_proxyAddr) k).trans (hPool k))
  · -- the pool is still clean: `CleanPool` reads only proxy storage, preserved above
    have hpres : ∀ k, storOf attackerPost.state proxyAddr k = storOf postC.state proxyAddr k :=
      fun k => (storOf_of_create_ne hArest (Ne.symm attackerAddr_ne_proxyAddr) k).trans
        (storOf_of_create_ne hTrest (Ne.symm tokenAddr_ne_proxyAddr) k)
    unfold CleanPool at hclean ⊢
    simp only [hpres]; exact hclean

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
