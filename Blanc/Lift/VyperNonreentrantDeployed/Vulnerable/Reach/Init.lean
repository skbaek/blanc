import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitTop

/-! # V− setup, messages 1–3: creations and the executed initializer

`setup_initialize` composes the implementation creation, the synthetic clone creation and the
root call of `initialize` through the clone, each message starting from exactly the previous
message's settled world, from the disclosed initial world (the funded code-free creator only),
on every covered fork with exact gas. Nothing about the initializer's outcome is assumed: its
success, its gas and the complete resulting proxy storage are derived from the run.

The resulting pool satisfies `CleanPool`: zero reserves (`balances`, slots 8 and 9), zero LP
supply (`totalSupply`, slot 26), all five per-function locks (slots 0–4) released, the
configuration the arguments ask for, and an empty LP footprint — every nonzero proxy slot is
one of the eleven configuration slots `configSlots`, so no `balanceOf`/`allowance` entry was
written. (This is a statement about slots: that no mapping key of an arbitrary address hashes
to a configuration slot is a hash fact outside the finite observation.) The implementation's
storage stays `{10 ↦ 31337}`, separate from the pool's. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun

/-- The proxy slots `initialize` leaves nonzero: `factory` (5), `coins` (6, 7), `initial_A`
and `future_A` (11, 12), `rate_multipliers` (15, 16), `name` (length 17, data 18) and
`symbol` (length 21, data 22). -/
def configSlots : List B256 := [5, 6, 7, 11, 12, 15, 16, 17, 18, 21, 22]

/-- **A clean, initialized pool at `proxyAddr`**: zero reserves and LP supply, the five locks
released, every nonzero storage slot a configuration slot (no LP balance or allowance entry),
and the configuration `initialize("", "", [ETH, T, 0, 0], [1e18, 1e18, 0, 0], 100, 0)` from
`creator` sets. -/
def CleanPool (W : State) : Prop :=
  storOf W proxyAddr 8 = 0 ∧ storOf W proxyAddr 9 = 0 ∧ storOf W proxyAddr 26 = 0 ∧
  (∀ i ∈ ([0, 1, 2, 3, 4] : List B256), storOf W proxyAddr i = 0) ∧
  (∀ k, storOf W proxyAddr k ≠ 0 → k ∈ configSlots) ∧
  storOf W proxyAddr 5 = creator.toNat.toB256 ∧ storOf W proxyAddr 6 = ethCoin.toNat.toB256 ∧
  storOf W proxyAddr 7 = tokenAddr.toNat.toB256 ∧ storOf W proxyAddr 10 = 0 ∧
  storOf W proxyAddr 11 = 10000 ∧ storOf W proxyAddr 12 = 10000 ∧
  storOf W proxyAddr 15 = 1000000000000000000 ∧ storOf W proxyAddr 16 = 1000000000000000000

theorem stor2_absent : ∀ e ∈ stor2, e.1.1 ≠ proxyAddr := by decide

theorem initWrites_at : ∀ e ∈ initWrites, e.1.1 = proxyAddr := by decide

theorem initWrites_footprint (k : B256) (hk : k ∉ configSlots) : lookupS initWrites proxyAddr k = 0 := by
  refine lookupS_eq_zero_of fun e he hek => ?_
  simp only [initWrites, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (simp only [Prod.mk.injEq, true_and] at hek
       subst hek
       exact absurd (by decide) hk)

theorem precompAcs_restate : ∀ e ∈ precompAcs, e.2 = lookupA acs3 e.1 := by
  intro e he
  simp only [precompAcs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem acs3_split : acs3 = [(proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
    (creator, ⟨0, creatorFunds, .empty, .empty⟩)] ++ acs2 := by
  kernel_rfl

theorem acs3_restate : ∀ e ∈ ([(proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
    (creator, ⟨0, creatorFunds, .empty, .empty⟩)] : AcctShadow), e.2 = lookupA acs2 e.1 := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

/-- The settled world of message 3, read off: the proxy's storage is `initWrites`, every other
address keeps `world2`'s storage, every account keeps its view. -/
theorem init_world_facts {post : Devm}
    (hs : ∀ a k, storOf post.state a k = lookupS (initWrites ++ stor2) a k)
    (ha : AcctAgree post.state (precompAcs ++ acs3)) :
    (∀ k, storOf post.state proxyAddr k = lookupS initWrites proxyAddr k) ∧
    (∀ a, a ≠ proxyAddr → ∀ k, storOf post.state a k = storOf world2 a k) ∧
    (∀ a, acctView (post.state.get a) = acctView (world2.get a)) := by
  refine ⟨fun k => (hs _ k).trans (lookupS_append_of_absent stor2_absent k),
    fun a hne k => ?_, fun a => ?_⟩
  · rw [hs, lookupS_append_of_ne (fun e he h => hne (h.symm.trans (initWrites_at e he))), storAgree2]
  · rw [ha a, lookupA_append_of_restate precompAcs_restate, acs3_split,
      lookupA_append_of_restate acs3_restate, acctAgree2 a]

theorem cleanPool_of {W : State} (h : ∀ k, storOf W proxyAddr k = lookupS initWrites proxyAddr k) :
    CleanPool W := by
  have hz : ∀ k, k ∉ configSlots → storOf W proxyAddr k = 0 := fun k hk =>
    (h k).trans (initWrites_footprint k hk)
  have hl : ∀ i ∈ ([0, 1, 2, 3, 4] : List B256), i ∉ configSlots := by decide
  refine ⟨hz _ (by decide), hz _ (by decide), hz _ (by decide), fun i hi => hz _ (hl i hi),
    fun k hk => Classical.byContradiction fun hn => hk (hz k hn), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [h]; decide

/-- **V− setup, messages 1–3, every covered fork.** From the disclosed initial world, the
preserved implementation creation, the synthetic clone creation from exactly its settled
world, and the root call of `initialize` through the clone from exactly the clone's settled
world all succeed with exact gas. The call runs the clone's installed code, and it consumes
the initializer's guard `fee == 0` against the clone's own (empty) storage while the
implementation holds the sentinel `fee = 31337`. The settled pool storage is exactly
`initWrites` (a clean pool), the implementation keeps `{10 ↦ 31337}`, every other address keeps
its storage, and no account's nonce, balance or code changes. -/
theorem setup_initialize (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postC : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      postI.gasLeft = 466978 ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      postP.error = none ∧ postP.gasLeft = 90972 ∧
      postP.state.get implAddr = implAccount ∧ postP.state.get proxyAddr = proxyAccount ∧
      (∀ a, a ≠ implAddr → a ≠ proxyAddr → postP.state.get a = initialWorld.get a) ∧
      (initMsg fork postP.state).code = postP.state.getCode proxyAddr ∧
      storOf postP.state proxyAddr 10 = 0 ∧ storOf postP.state implAddr 10 = 31337 ∧
      processMessage (initMsg fork postP.state) = .ok postC ∧ postC.error = none ∧
      postC.gasLeft = 744993 ∧ postC.output = [] ∧
      (∀ k, storOf postC.state proxyAddr k = lookupS initWrites proxyAddr k) ∧
      (∀ a, a ≠ proxyAddr → ∀ k, storOf postC.state a k = storOf postP.state a k) ∧
      (∀ a, acctView (postC.state.get a) = acctView (postP.state.get a)) ∧
      storOf postC.state implAddr 10 = 31337 ∧
      CleanPool postC.state := by
  obtain ⟨postI, postP, h1, e1, g1, -, -, -, h2, e2, g2, hI, hP, hF, hS⟩ :=
    setup_creations fork hfork initialWorld initialWorld_absent.1 initialWorld_absent.2
  have hw : postP.state = world2 := hS
  obtain ⟨postC, h3, e3', g3, o3, hs, ha⟩ := init_message_at (g := fork) hfork
  obtain ⟨hpool, hrest, hview⟩ := init_world_facts hs ha
  have himpl : storOf postC.state implAddr 10 = 31337 := by
    rw [hrest implAddr (by decide), ← hw, storOf, hI]; rfl
  refine ⟨postI, postP, postC, h1, e1, g1, h2, e2, g2, hI, hP, hF, ?_, ?_, ?_, by rw [hw]; exact h3,
    e3', g3, o3, hpool, fun a ha' k => by rw [hw]; exact hrest a ha' k,
    fun a => by rw [hw]; exact hview a, himpl, cleanPool_of hpool⟩
  · show fwdCode = (postP.state.get proxyAddr).code
    rw [hP]; rfl
  · rw [storOf, hP]; rfl
  · rw [storOf, hI]; rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
