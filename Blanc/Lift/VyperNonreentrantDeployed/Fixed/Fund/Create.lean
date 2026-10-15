import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.World

/-! # V+ messages 5 and 6: executed CREATEs of the token and the receiver

From the clean pool `world4`, the code-free `creator` creates the shared synthetic token at
`tokenAddr` (its constructor mints `balanceOf[creator] := 10^6`, `Token20.Creation.create_token`)
and then, from that settled world, the labelled synthetic receiver at `receiverAddr`
(`ReceiverR.Creation.create_receiver`), on every covered fork, with exact gas.  The settled
worlds are the closed terms `world5` and `world6`, and the shadows `acs6`/`stor5` describe
`world6` at every address and key. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

theorem tokenAddr_ne : tokenAddr ≠ proxyAddr ∧ tokenAddr ≠ implAddr ∧ tokenAddr ≠ creator := by
  decide

theorem receiverAddr_ne : receiverAddr ≠ proxyAddr ∧ receiverAddr ≠ implAddr ∧
    receiverAddr ≠ creator ∧ receiverAddr ≠ tokenAddr := by
  decide

theorem stor_empty_set_get (c k : B256) (v : B256) :
    (Stor.empty.set c v).get k = if c = k then v else 0 := by
  by_cases h : c = k
  · subst h; rw [Stor.get_set_self, ite_eq_left rfl]
  · rw [Stor.get_set_ne _ h, stor_empty_get, ite_eq_right h]

/-- The shadows that describe the world after both creations. -/
theorem acs6_eq (a : Adr) :
    lookupA ((receiverAddr, receiverAccount) :: (tokenAddr, tokenAccount) :: acs0) a =
      lookupA acs6 a := by
  refine lookupA_eq_of_keys (fun b hb => ?_) a
  have hk : ((receiverAddr, receiverAccount) :: (tokenAddr, tokenAccount) :: acs0).map Prod.fst ++
      acs6.map Prod.fst = [receiverAddr, tokenAddr, creator, proxyAddr, implAddr, receiverAddr,
        tokenAddr, creator, proxyAddr, implAddr] := rfl
  rw [hk] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/- Keep the input world abstract while constructing the creation evidence. -/
private theorem create_fixtures_from (W4 : State) (fork : Fork) (hfork : CoveredFork fork)
    (hW : WorldIs W4 acs0 storOracle) :
    let W5 := ((CreateEntry.entryState W4 creator tokenAddr).setStorVal tokenAddr
      creator.toB256 1000000).setCode tokenAddr
        Blanc.Lift.VyperNonreentrantDeployed.Token20.code
    let W6 := (CreateEntry.entryState W5 creator receiverAddr).setCode receiverAddr
      Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code
    ∃ postT postR : Devm,
      processCreateMessage (tokenCreateMsg fork W4) = .ok postT ∧ postT.error = none ∧
      postT.gasLeft = 118019 ∧ postT.state = W5 ∧
      processCreateMessage (receiverCreateMsg fork W5) = .ok postR ∧ postR.error = none ∧
      postR.gasLeft = 82166 ∧ postR.state = W6 ∧
      WorldIs W6 acs6 stor5 := by
  intro W5 W6
  obtain ⟨hTP, hTI, hTC⟩ := tokenAddr_ne
  obtain ⟨hRP, hRI, hRC, hRT⟩ := receiverAddr_ne
  -- the token creation
  obtain ⟨postT, hT, hTe, hTg, hTtok, hTrest, hTstate⟩ :=
    Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.create_token (tokenCreateMsg fork W4)
      hfork rfl rfl rfl rfl rfl (by show (82000 : Nat) ≤ 200000; decide)
  have hv4 : acctView (W4.get tokenAddr) = Acct.nil := (hW.1 tokenAddr).trans rfl
  have hmint : Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.mintSstoreGas
      (tokenCreateMsg fork W4) = 22100 := by
    have h2 : (tokenCreateMsg fork W4).currentTarget = tokenAddr := rfl
    have h3 : (tokenCreateMsg fork W4).caller = creator := rfl
    have h4 : (tokenCreateMsg fork W4).accessedStorageKeys = .emptyWithCapacity := rfl
    unfold Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.mintSstoreGas
    rw [h2, h3, h4, ite_eq_right Std.HashSet.not_mem_emptyWithCapacity]
    rfl
  have hw5 : postT.state = W5 := hTstate
  have hTacct : postT.state.get tokenAddr =
      Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.tokenAcct W4 tokenAddr creator :=
    hTtok
  -- the receiver creation
  obtain ⟨postR, hR, hRe, hRg, hRacc, hRrest, hRstate⟩ :=
    Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.create_receiver
      (receiverCreateMsg fork W5) hfork rfl rfl rfl rfl (by show (17834 : Nat) ≤ 100000; decide)
  have hw6 : postR.state = W6 := by rw [hRstate]; rfl
  have hRacct : postR.state.get receiverAddr =
      Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.receiverAcct W5
        receiverAddr := hRacc
  -- the shadows of `W5`
  have hW5 : WorldIs W5 ((tokenAddr, tokenAccount) :: acs0) stor5 := by
    have h := worldIs_install (stor' := stor5) hW (hw5 ▸ hTacct)
      (fun a ha => hw5 ▸ hTrest a ha) (fun k => by
        show (Stor.empty.set creator.toB256 1000000).get k = lookupS stor5 tokenAddr k
        rw [stor_empty_set_get]
        by_cases hk : creator.toB256 = k
        · rw [ite_eq_left hk]; simp only [stor5, lookupS, true_and, hk, ↓reduceIte]
        · rw [ite_eq_right hk]
          simp only [stor5, lookupS, true_and, hk, ↓reduceIte]
          exact (lookupS_storOracle_ne hTP hTI k).symm)
      (fun a k ha => by simp only [stor5, lookupS, Ne.symm ha, false_and, ↓reduceIte])
    have hview : acctView (Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.tokenAcct W4
        tokenAddr creator) = tokenAccount := by
      have hn : (W4.get tokenAddr).nonce = 0 := congrArg Acct.nonce hv4
      have hb : (W4.get tokenAddr).bal = 0 := congrArg Acct.bal hv4
      simp only [Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.tokenAcct, acctView, hn, hb,
        tokenAccount]
      rfl
    rw [hview] at h
    exact h
  -- the shadows of `W6`
  have hv5 : acctView (W5.get receiverAddr) = Acct.nil := by
    rw [← hw5, hTrest receiverAddr hRT]
    exact (hW.1 receiverAddr).trans rfl
  have hW6 : WorldIs W6 acs6 stor5 := by
    have h := worldIs_install (stor' := stor5) hW5 (hw6 ▸ hRacct)
      (fun a ha => hw6 ▸ hRrest a ha) (fun k => by
        show Stor.empty.get k = lookupS stor5 receiverAddr k
        rw [stor_empty_get]
        simp only [stor5, lookupS, hRT.symm, false_and, ↓reduceIte]
        exact (lookupS_storOracle_ne hRP hRI k).symm)
      (fun a k _ => rfl)
    have hview : acctView (Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.receiverAcct
        W5 receiverAddr) = receiverAccount := by
      have hn : (W5.get receiverAddr).nonce = 0 := congrArg Acct.nonce hv5
      have hb : (W5.get receiverAddr).bal = 0 := congrArg Acct.bal hv5
      simp only [Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.receiverAcct, acctView,
        hn, hb, receiverAccount]
      rfl
    rw [hview] at h
    exact ⟨fun a => (h.1 a).trans (acs6_eq a), h.2⟩
  refine ⟨postT, postR, hT, hTe, ?_, hw5, hw5 ▸ hR, hRe, ?_, hw6, hW6⟩
  · have hg : (tokenCreateMsg fork W4).gas = 200000 := rfl
    rw [hTg, hmint, hg]
  · have hg : (receiverCreateMsg fork W5).gas = 100000 := rfl
    rw [hRg, hg]

/-- **Messages 5 and 6**, every covered fork, from the clean pool `world4`: the token CREATE
leaves 118,019 of its 200,000 gas and settles to `world5`; the receiver CREATE from `world5`
leaves 82,166 of its 100,000 gas and settles to `world6`; the shadows `acs6`/`stor5` describe
`world6` (the token holds the mint `balanceOf[creator] = 10^6`, both fixtures hold their
registered runtimes). -/
theorem create_fixtures (fork : Fork) (hfork : CoveredFork fork)
    (hW : WorldIs world4 acs0 storOracle) :
    ∃ postT postR : Devm,
      processCreateMessage (tokenCreateMsg fork world4) = .ok postT ∧ postT.error = none ∧
      postT.gasLeft = 118019 ∧ postT.state = world5 ∧
      processCreateMessage (receiverCreateMsg fork world5) = .ok postR ∧ postR.error = none ∧
      postR.gasLeft = 82166 ∧ postR.state = world6 ∧
      WorldIs world6 acs6 stor5 := by
  exact create_fixtures_from world4 fork hfork hW

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
