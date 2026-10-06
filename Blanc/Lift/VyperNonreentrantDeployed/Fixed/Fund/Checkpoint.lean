import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Add
import Blanc.LedgerConservation

/-! # V+ V3: the funded checkpoint, reached by execution, with a sound LP ledger

`setup_funded`: from the disclosed `initialWorld`, on every covered fork, the eight messages
(implementation CREATE, synthetic clone CREATE, `initialize`, `set_oracle(0, 0)`, token CREATE,
receiver CREATE, `approve`, the first `add_liquidity`) each succeed from exactly the previous
settled world, with exact gas, and reach a world described by `Checkpoint`.

`checkpoint_facts` reads that world: the **sound LP ledger** `totalSupply = Σ_{h ∈ {creator}}
balanceOf[h]` (2000 = 2000; the creator is the only account any setup message credits with LP
tokens), the raw support of the clone's storage (every nonzero slot is a named field or the
creator's LP entry at `keccak256(20 ‖ creator)`), concrete slot separation, the held assets
(1000 wei and `T.balanceOf[P] = 1000`), zero admin balances (slots 4, 5; V+ keeps no separate
reserves: its pool balances are the held balances less these), and the token's own ledger. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

/-- **The funded checkpoint**: every account view as `acsAdd` (the creator, the clone with
1000 wei, the implementation, the token, the receiver) and exactly the storage `storAdd`. -/
def Checkpoint (W : State) : Prop := WorldIs W acsAdd storAdd

/-- The clone's fields the setup leaves nonzero, then the creator's LP entry. -/
def poolSlots : List B256 :=
  [0, 0x16, lpSlot creator, 0x17, 0x13, 0x12, 0x10, 0x0f, 0x1b, 0x19, 0x1a, 0x01, 0x0a, 0x09,
    0x03, 0x02]

theorem bal_of_worldIs {W : State} {acs : AcctShadow} {stor : StorShadow} (h : WorldIs W acs stor)
    (a : Adr) : (W.get a).bal = (lookupA acs a).bal := by
  have := congrArg Acct.bal (h.1 a); exact this

theorem code_of_worldIs {W : State} {acs : AcctShadow} {stor : StorShadow} (h : WorldIs W acs stor)
    (a : Adr) : (W.get a).code = (lookupA acs a).code := by
  have := congrArg Acct.code (h.1 a); exact this

/-- What the funded checkpoint holds. -/
theorem checkpoint_facts {W : State} (h : Checkpoint W) :
    -- the sound LP ledger over the footprint `{creator}`
    (storOf W proxyAddr 0x16).toNat =
      ledgerSumOn {creator} (fun holder => storOf W proxyAddr (lpSlot holder)) ∧
    storOf W proxyAddr 0x16 = 2000 ∧ storOf W proxyAddr (lpSlot creator) = 2000 ∧
    -- the lock released, zero admin balances
    storOf W proxyAddr 0 = 3 ∧ storOf W proxyAddr 4 = 0 ∧ storOf W proxyAddr 5 = 0 ∧
    -- held assets
    (W.get proxyAddr).bal = 1000 ∧ storOf W tokenAddr proxyAddr.toB256 = 1000 ∧
    storOf W tokenAddr creator.toB256 = 999000 ∧
    (W.get creator).bal = creatorFunds - 1000 ∧
    storOf W tokenAddr allowCP = 0 ∧
    -- the token's ledger: the minted supply, held by the creator and the clone
    ledgerSumOn {creator, proxyAddr} (fun holder => storOf W tokenAddr holder.toB256) = 1000000 ∧
    -- raw support and concrete separation
    (∀ k, storOf W proxyAddr k ≠ 0 → k ∈ poolSlots) ∧
    lpSlot creator ∉ poolSlots.tail.tail.tail ∧ lpSlot creator ≠ 0 ∧ lpSlot creator ≠ 0x16 ∧
    lpSlot creator ≠ 4 ∧ lpSlot creator ≠ 5 ∧
    (∀ k, storOf W tokenAddr k ≠ 0 → k = proxyAddr.toB256 ∨ k = creator.toB256) ∧
    (∀ k, storOf W implAddr k = if k = 1 then 1 else 0) ∧
    (∀ a, a ≠ proxyAddr → a ≠ implAddr → a ≠ tokenAddr → ∀ k, storOf W a k = 0) ∧
    -- the codes
    (W.get proxyAddr).code = fwd ∧ (W.get implAddr).code = code ∧
    (W.get tokenAddr).code = Blanc.Lift.VyperNonreentrantDeployed.Token20.code ∧
    (W.get receiverAddr).code = Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code := by
  have hs := h.2
  have hsup : storOf W proxyAddr 0x16 = 2000 := by rw [hs]; decide +kernel
  have hlp : storOf W proxyAddr (lpSlot creator) = 2000 := by rw [hs]; decide +kernel
  have htP : storOf W tokenAddr proxyAddr.toB256 = 1000 := by rw [hs]; decide +kernel
  have htC : storOf W tokenAddr creator.toB256 = 999000 := by rw [hs]; decide +kernel
  refine ⟨?_, hsup, hlp, by rw [hs]; decide +kernel, by rw [hs]; decide +kernel,
    by rw [hs]; decide +kernel, (bal_of_worldIs h proxyAddr).trans rfl, htP, htC,
    (bal_of_worldIs h creator).trans rfl, by rw [hs]; decide +kernel, ?_, fun k hk => ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun k hk => ?_, fun k => ?_, fun a haP haI haT k => ?_, (code_of_worldIs h _).trans rfl,
    (code_of_worldIs h _).trans rfl, (code_of_worldIs h _).trans rfl,
    (code_of_worldIs h _).trans rfl⟩
  · rw [ledgerSumOn, Finset.sum_singleton, hsup, hlp]
  · have hne : creator ≠ proxyAddr := by decide
    rw [ledgerSumOn, Finset.sum_pair hne, htP, htC]
    rfl
  · rw [hs] at hk
    have hm := lookupS_ne_zero_mem hk
    have hPI : (proxyAddr = implAddr) = False := by decide
    have hPT : (proxyAddr = tokenAddr) = False := by decide
    simp only [storAdd, storOracle, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_and, hPI,
      hPT, false_and, false_or] at hm
    simp only [poolSlots, List.mem_cons, List.not_mem_nil, or_false]
    exact hm
  · rw [hs] at hk
    have hm := lookupS_ne_zero_mem hk
    have hTI : (tokenAddr = implAddr) = False := by decide
    have hTP : (tokenAddr = proxyAddr) = False := by decide
    simp only [storAdd, storOracle, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_and, hTI,
      hTP, false_and, false_or] at hm
    exact hm
  · rw [hs]
    by_cases hk : k = 1
    · subst hk; decide +kernel
    · have hk' : ((1 : B256) = k) = False := eq_false (Ne.symm hk)
      have hIP : (implAddr = proxyAddr) = False := by decide
      have hIT : (implAddr = tokenAddr) = False := by decide
      have hPI : (proxyAddr = implAddr) = False := by decide
      have hTI : (tokenAddr = implAddr) = False := by decide
      simp only [storAdd, storOracle, List.cons_append, List.nil_append, lookupS, hPI, hTI,
        false_and, ↓reduceIte, hk', and_false, hk]
  · rw [hs]
    by_contra hne
    have hm := lookupS_ne_zero_mem hne
    simp only [storAdd, storOracle, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ |
      ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ |
      ⟨e, -⟩
    all_goals first | exact haP e | exact haI e | exact haT e

/-- The clean pool `set_oracle` leaves, as the closed world `world4`. -/
theorem world4_eq : world4 = (dO world3).state := by unfold world4; rfl

theorem world7_eq : world7 = dA.state := by unfold world7; rfl

/-- **V+ V3: the funded checkpoint is reached by execution**, on every covered fork.  From the
disclosed `initialWorld`, eight messages each succeed from exactly the previous settled world
(the setup's four, then the token CREATE minting the creator's 10^6, the receiver CREATE,
`T.approve(P, 1000)`, and `P.add_liquidity([1000, 1000], 0)` with 1000 wei, whose pool body reads
`T.balanceOf(P)` by `STATICCALL` and pulls the token by `transferFrom`), with exact gas; the
reached world is the `Checkpoint`.  Nothing about the token's replies, the minted amount or the
post-state is assumed. -/
theorem setup_funded (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postInit postOracle postT postR postA postD : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postInit ∧ postInit.error = none ∧
      postInit.gasLeft = 679367 ∧
      processMessage (oracleMsg fork postInit.state) = .ok postOracle ∧ postOracle.error = none ∧
      postOracle.gasLeft = 89070 ∧ CleanPool postOracle.state ∧
      processCreateMessage (tokenCreateMsg fork postOracle.state) = .ok postT ∧
      postT.error = none ∧ postT.gasLeft = 118019 ∧
      processCreateMessage (receiverCreateMsg fork postT.state) = .ok postR ∧
      postR.error = none ∧ postR.gasLeft = 82166 ∧
      processMessage (approveMsg fork postR.state) = .ok postA ∧ postA.error = none ∧
      postA.gasLeft = 77697 ∧
      processMessage (addMsg fork postA.state) = .ok postD ∧ postD.error = none ∧
      postD.gasLeft = 871140 ∧ postD.refundCounter = 4800 ∧
      Checkpoint postD.state ∧ postD = dD := by
  obtain ⟨postI, postP, postInit, postOracle, h1, e1, h2, e2, hWP, -, -, -, h3, e3, g3, -, hWI, -,
    h4, e4, g4, -, hclean⟩ := setup_init fork hfork
  -- the setup's settled machines are the closed ones
  obtain ⟨-, hs⟩ := setup_creations_exact fork hfork initialWorld postI postP h1 h2
  have hw2 : postP.state = world2 := hs
  have hW2 : WorldIs world2 acs0 stor0 := hw2 ▸ hWP
  have hI : postInit = dI world2 := by
    have h3' : processMessage (initMsg fork world2) = .ok postInit := by rw [hw2] at h3; exact h3
    exact Except.ok.inj (h3'.symm.trans (init_run fork hfork hW2).1)
  have hW3 : WorldIs world3 acs0 storInit := by rw [hI] at hWI; exact hWI
  have h4' : processMessage (oracleMsg fork world3) = .ok postOracle := by rw [hI] at h4; exact h4
  have hO : postOracle = dO world3 := by
    exact Except.ok.inj (h4'.symm.trans (oracle_run fork hfork hW3).1)
  have hw4 : postOracle.state = world4 := by rw [hO, world4_eq]
  have hW4 : WorldIs world4 acs0 storOracle := hw4 ▸ hclean
  -- messages 5 and 6
  obtain ⟨postT, postR, h5, e5, g5, hw5, h6, e6, g6, hw6, hW6⟩ := create_fixtures fork hfork hW4
  -- message 7
  obtain ⟨h7, e7, g7, -, hW7⟩ := approve_run fork hfork hW6
  -- message 8
  have hW7' : WorldIs world7 acs6 stor7 := by rw [world7_eq]; exact hW7
  obtain ⟨h8, e8, g8, r8, hW8⟩ := add_run fork hfork hW7'
  refine ⟨postI, postP, postInit, postOracle, postT, postR, dA, dD, h1, e1, h2, e2, h3, e3, g3,
    h4, e4, g4, hclean, by rw [hw4]; exact h5, e5, g5, by rw [hw5]; exact h6, e6, g6,
    by rw [hw6]; exact h7, e7, g7, by rw [← world7_eq]; exact h8, e8, g8, r8, hW8, rfl⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
