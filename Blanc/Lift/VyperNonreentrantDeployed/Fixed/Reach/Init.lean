import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Top
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.OracleTop

/-! # V+ setup, messages 1–4: creations, `initialize` and `set_oracle(0, 0)`

From the disclosed `initialWorld` (only the funded creator), on every covered fork: the
implementation creation, the synthetic clone creation, the actual `initialize` through the
clone, and the mandatory `set_oracle(0x00000000, 0x0)` through the clone (the initializer sets
`originator := tx.origin`, which `_stored_rates` requires to be cleared), each from exactly the
previous message's settled world, all succeed.  `CleanPool` is derived from these runs; no
initializer success or post-state is assumed. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

/-- A nonzero read names its address and key in the log. -/
theorem lookupS_ne_zero_mem {l : StorShadow} {a : Adr} {k : B256} (h : lookupS l a k ≠ 0) :
    (a, k) ∈ l.map Prod.fst := by
  induction l with
  | nil => exact absurd rfl h
  | cons e l ih =>
    obtain ⟨⟨a', k'⟩, v⟩ := e
    simp only [lookupS] at h
    split at h
    · rename_i hh
      obtain ⟨rfl, rfl⟩ := hh
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem stor_empty_get (k : B256) : Stor.empty.get k = 0 := by
  rw [Stor.get_eq_getD_find?, Stor.find?_empty]; rfl

theorem initialWorld_get_ne {a : Adr} (h : a ≠ creator) : initialWorld.get a = .nil := by
  unfold initialWorld
  rw [State.get_set_ne _ (Ne.symm h)]
  rfl

theorem initialWorld_get_creator : initialWorld.get creator = creatorAccount := by
  unfold initialWorld
  rw [State.get_set_self]
  rfl

/-- **The creations leave the world `acs0`/`stor0` describe.** -/
theorem worldIs_creations {W : State} (hI : W.get implAddr = implAccount)
    (hP : W.get proxyAddr = proxyAccount)
    (hO : ∀ a, a ≠ implAddr → a ≠ proxyAddr → W.get a = initialWorld.get a) :
    WorldIs W acs0 stor0 := by
  have hIC : implAddr ≠ creator := by decide
  have hPC : proxyAddr ≠ creator := by decide
  have hIP : implAddr ≠ proxyAddr := by decide
  refine ⟨fun a => ?_, fun a k => ?_⟩
  · by_cases ha : a = implAddr
    · subst ha; rw [hI]; rfl
    by_cases hb : a = proxyAddr
    · subst hb; rw [hP]; rfl
    by_cases hc : a = creator
    · subst hc; rw [hO _ ha hb, initialWorld_get_creator]; rfl
    rw [hO _ ha hb, initialWorld_get_ne hc]
    simp only [acs0, accts0, acctShadowOf, List.foldl, lookupA, Ne.symm ha, Ne.symm hb,
      Ne.symm hc, ↓reduceIte]
    rfl
  · unfold storOf
    by_cases ha : a = implAddr
    · subst ha
      rw [hI]
      show (Stor.empty.set 1 1).get k = lookupS [((implAddr, 1), 1)] implAddr k
      by_cases hk : (1 : B256) = k
      · subst hk; rw [Stor.get_set_self]; simp only [lookupS, and_self, ↓reduceIte]
      · rw [Stor.get_set_ne _ hk, stor_empty_get]
        simp only [lookupS, true_and, hk, ↓reduceIte]
    have hl : lookupS stor0 a k = 0 := by
      simp only [stor0, lookupS, Ne.symm ha, false_and, ↓reduceIte]
    rw [hl]
    by_cases hb : a = proxyAddr
    · subst hb; rw [hP]; exact stor_empty_get k
    by_cases hc : a = creator
    · subst hc; rw [hO _ ha hb, initialWorld_get_creator]; exact stor_empty_get k
    rw [hO _ ha hb, initialWorld_get_ne hc]; exact stor_empty_get k

/-- **The clean pool**, as the setup calls leave it: every account as the creations left it
(the funded creator, the implementation with `factory = 1`, the clone's forwarder), and exactly
the storage `storOracle`. -/
def CleanPool (W : State) : Prop := WorldIs W acs0 storOracle

/-- What the clean pool holds at the clone: the lock is released (slot 0 is 0), `totalSupply`
(slot `0x16`) is 0, `factory = creator`, `coins = [ETH, T]`, `initial_A = future_A = 100`,
`fee = 0`, `oracle_method = 0`, `originator = 0`, the moving-average fields, the name and
symbol words, `DOMAIN_SEPARATOR`; every nonzero slot of the clone is one of these; the
implementation's storage is `{1 ↦ 1}`. -/
theorem cleanPool_facts {W : State} (h : CleanPool W) :
    storOf W proxyAddr 0 = 0 ∧ storOf W proxyAddr 0x16 = 0 ∧
    storOf W proxyAddr 1 = creator.toNat.toB256 ∧
    storOf W proxyAddr 2 = ethSentinel.toB256 ∧ storOf W proxyAddr 3 = tokenAddr.toNat.toB256 ∧
    storOf W proxyAddr 6 = 0 ∧ storOf W proxyAddr 9 = (100 : Nat).toB256 ∧
    storOf W proxyAddr 0x0a = (100 : Nat).toB256 ∧ storOf W proxyAddr 0x0d = 0 ∧
    storOf W proxyAddr 0x0e = 0 ∧ storOf W proxyAddr 0x0f = (23 : Nat).toB256 ∧
    storOf W proxyAddr 0x10 = leftWord nameBytes ∧ storOf W proxyAddr 0x12 = (2 : Nat).toB256 ∧
    storOf W proxyAddr 0x13 = leftWord symbolBytes ∧ storOf W proxyAddr 0x17 = domainSeparator ∧
    storOf W proxyAddr 0x19 = packedPrices ∧ storOf W proxyAddr 0x1a = (866 : Nat).toB256 ∧
    storOf W proxyAddr 0x1b = timeV2 ∧
    (∀ k, storOf W proxyAddr k ≠ 0 →
      k ∈ ([0x17, 0x13, 0x12, 0x10, 0x0f, 0x1b, 0x19, 0x1a, 0x01, 0x0a, 0x09, 0x03, 0x02] :
        List B256)) ∧
    (∀ k, storOf W implAddr k = if k = 1 then 1 else 0) ∧
    (∀ a, a ≠ proxyAddr → a ≠ implAddr → ∀ k, storOf W a k = 0) := by
  have hs := h.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_,
    fun k => ?_, fun a haP haI k => ?_⟩
  all_goals first
    | (rw [hs]; decide +kernel)
    | skip
  · rw [hs] at hk
    have hm := lookupS_ne_zero_mem hk
    have hPI : (proxyAddr = implAddr) = False := by decide
    simp only [storOracle, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, true_and, hPI, false_and] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hm
  · rw [hs]
    by_cases hk : k = 1
    · subst hk; decide +kernel
    · have hPI : (proxyAddr = implAddr) = False := by decide
      have hk' : ((1 : B256) = k) = False := eq_false (Ne.symm hk)
      simp only [storOracle, lookupS, hPI, false_and, ↓reduceIte, hk', and_false, hk]
  · rw [hs]
    by_contra hne
    have hm := lookupS_ne_zero_mem hne
    simp only [storOracle, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    all_goals first | exact haP h | exact haI h

/-- **The V+ setup through `set_oracle`**, on every covered fork: from the disclosed
`initialWorld`, the implementation creation, the synthetic clone creation, the actual
`initialize` through the clone and the mandatory `set_oracle(0, 0)` through the clone each
succeed, each from exactly the previous settled world, with exact gas; the final world is the
`CleanPool`. -/
theorem setup_init (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postInit postOracle : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      WorldIs postP.state acs0 stor0 ∧
      (initMsg fork postP.state).code = postP.state.getCode proxyAddr ∧
      storOf postP.state proxyAddr 1 = 0 ∧ storOf postP.state implAddr 1 = 1 ∧
      processMessage (initMsg fork postP.state) = .ok postInit ∧ postInit.error = none ∧
      postInit.gasLeft = 679367 ∧ postInit.refundCounter = 0 ∧
      WorldIs postInit.state acs0 storInit ∧
      storOf postInit.state proxyAddr 0x0e = creator.toNat.toB256 ∧
      processMessage (oracleMsg fork postInit.state) = .ok postOracle ∧
      postOracle.error = none ∧ postOracle.gasLeft = 89070 ∧ postOracle.refundCounter = 4800 ∧
      CleanPool postOracle.state := by
  obtain ⟨postI, postP, h1, e1, -, -, -, h2, e2, -, hI, hP, hF⟩ :=
    setup_creations fork hfork initialWorld initialWorld_absent.1 initialWorld_absent.2
  have hW0 := worldIs_creations hI hP hF
  obtain ⟨-, hs⟩ := setup_creations_exact fork hfork initialWorld postI postP h1 h2
  have hw2 : postP.state = world2 := hs
  rw [hw2] at hW0
  obtain ⟨h3, e3, g3, r3, hW1⟩ := init_run fork hfork hW0
  obtain ⟨h4, e4, g4, r4, hW2⟩ := oracle_run fork hfork hW1
  have hcode : (initMsg fork postP.state).code = postP.state.getCode proxyAddr := by
    show Blanc.forwarderCode Blanc.curvePlainImpl847e = (postP.state.get proxyAddr).code
    rw [hP]; rfl
  refine ⟨postI, postP, dI world2, dO world3, h1, e1, h2, e2, by rw [hw2]; exact hW0, hcode,
    by rw [hw2, hW0.2]; decide +kernel, by rw [hw2, hW0.2]; decide +kernel,
    by rw [hw2]; exact h3, e3, g3, r3, hW1, by rw [hW1.2]; decide +kernel, h4, e4, g4, r4, hW2⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
