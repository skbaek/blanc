import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Run
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy

/-!
# V+ setup message 3: `initialize` through the clone succeeds

`init_run`: from the creations' settled world `world2` (described by the shadows `acs0`,
`stor0`), the root call `initMsg g world2` (`initialize("", "", [ETH, T, 0, 0], [10^18, 10^18, 0, 0], 1, 0)` from
`creator` through the clone) succeeds on every covered fork with 679,367 of its 1,000,000 gas
left and no refund, and leaves a world with the same account views and exactly the storage
`storInit` (the clone's initialized slots and the implementation's `factory`).  No success or
post-state is assumed: the Prague walks of `Run.lean` are transported (`Proxy.lean`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

attribute [local irreducible] eI cI1 cpI eIB cIB1 cpId chId dIB2 cIB3 dIB dI2 cI3 dI

/-- **The implementation frame of `initialize`**, under any covered fork with the input
world's original storage: it walks to the identity `STATICCALL`, takes the precompile's
answer, walks to `STOP` and succeeds with `dIB world2`. -/
theorem frameIB {g : Fork} (hg : CoveredFork g) (hs : KOK (eIB world2).sta)
    (hag : PAgree (cIB0 world2)) :
    ∀ x, NodeAt ((eIB world2).sta.withFork g) (cIB0 world2) x →
      x.exn = .ok (dIB world2) ∧ ChildAgree (dIB world2) (cIB3 world2).keys (cIB3 world2).adrs (cIB3 world2).stor
        (cIB3 world2).acs := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, hst, -, wB1, pB1, dB1, hpId, hcaId, heId, hchId, hrId⟩ :=
    initFactsA
  obtain ⟨wB2, wB3, -⟩ := initFactsB
  have hcode : ((eIB world2).sta.withFork g).code = code := by
    simp only [Prod.mk.injEq] at hst; exact hst.2.2
  have w1 := (walk_transport hs hg (.avoid 0) codeTries okAny 393 (cIB0 world2)).trans wB1
  have w2 := (walk_transport hs hg (.avoid 0) codeTries okAny 154 (cIB2 world2)).trans wB2
  have w3 := (walk_transport hs hg (.avoid 0) codeTries okAny 1 (cIB3 world2)).trans wB3
  obtain ⟨hag1, h1⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 393 _ _ hag w1
  obtain ⟨x1, hx1, -, ex1, -, -⟩ := h1 x hx
  have hat : Ninst.At ((eIB world2).sta.withFork g).code (cIB1 world2).pc
      (.exec .staticcall) := by
    rw [hcode, pB1]; exact decodeT_sound codeTries dB1
  obtain ⟨sId, nId⟩ := scallDone_withFork hs.1 hg hpId
    (Frame.precompNeutral_of_codeAddress hcaId (by decide) (by decide)) heId
  obtain ⟨x2, -, hx2, ex2, -, hag2⟩ :=
    staticcall_done_node hx1 hag1 hat sId nId (by rw [hchId]; rfl) hrId
  obtain ⟨hag3, h3⟩ := pwalkH_cont (.avoid 0) codeTries hcode okAny 154 (cIB2 world2) _ hag2 w2
  obtain ⟨x3, hx3, -, ex3, -, -⟩ := h3 x2 hx2
  obtain ⟨ex4, -, -⟩ := pwalkH_halt (.avoid 0) codeTries hcode okAny 1 _ _ hag3 w3 x3 hx3
  exact ⟨by rw [← ex1, ← ex2, ← ex3]; exact ex4, halt1_childAgree codeTries hag3 w3⟩

/-- The account log the run leaves reads as the creations' world at every address. -/
theorem initAcs_eq (a : Adr) : lookupA (cI3 world2).acs a = lookupA acs0 a := by
  obtain ⟨-, hk, h4, hP, hC, hI⟩ := initFactsC
  refine lookupA_eq_of_keys (fun b hb => ?_) a
  have hk0 : acs0.map Prod.fst = [creator, proxyAddr, implAddr] := rfl
  rw [hk, hk0] at hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **Message 3, `initialize` through the clone**, on every covered fork, from the world the
creations leave (`world2`, which the creations' shadows describe): it settles to the closed
machine `dI world2` with no error, 679,367 gas left and no refund, and that world keeps every
account view and holds exactly the storage `storInit`. -/
theorem init_run (g : Fork) (hg : CoveredFork g) (hW : WorldIs world2 acs0 stor0) :
    processMessage (initMsg g world2) = .ok (dI world2) ∧ (dI world2).error = none ∧
      (dI world2).gasLeft = 679367 ∧ (dI world2).refundCounter = 0 ∧
      WorldIs (dI world2).state acs0 storInit := by
  obtain ⟨he, hst, w1, p1, d1, hp, heB, -, hca, -⟩ := initFactsA
  obtain ⟨-, -, hdB, hr, w3, w4, hdT, hgas, hrc⟩ := initFactsB
  obtain ⟨hcanon, -⟩ := initFactsC
  obtain ⟨hmsg, hca3⟩ := forwarder_root hg hW he hst w1 p1 d1 hp heB hca
    (fun hs hag => frameIB hg hs hag) hdB hr w3 w4 hdT
  refine ⟨hmsg, hdT, hgas, hrc, fun a => ?_, fun a k => ?_⟩
  · rw [← initAcs_eq a]; exact hca3.2.2.2 a
  · rw [hca3.2.2.1 a k, ← lookupS_canonS, hcanon]

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
