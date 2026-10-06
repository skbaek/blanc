import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.OracleRun
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy

/-!
# V+ setup message 4: `set_oracle(0, 0)` through the clone succeeds

`oracle_run`: from the world `initialize` leaves (`world3`, described by `acs0` and `storInit`),
the root call `oracleMsg g world3` from `creator` (the stored originator) succeeds on every covered
fork with 89,070 of its 100,000 gas left and a refund counter of 4,800, and leaves the same
account views and exactly the storage `storOracle` (the originator cleared, no oracle method).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

attribute [local irreducible] eO cO1 cpO eOB cOB1 dOB dO2 cO3 dO

/-- **The implementation frame of `set_oracle`**: it walks to `STOP` and succeeds. -/
theorem frameOB {g : Fork} (hg : CoveredFork g) (hs : KOK (eOB world3).sta)
    (hag : PAgree (cOB0 world3)) :
    ∀ x, NodeAt ((eOB world3).sta.withFork g) (cOB0 world3) x →
      x.exn = .ok (dOB world3) ∧ ChildAgree (dOB world3) (cOB1 world3).keys (cOB1 world3).adrs (cOB1 world3).stor
        (cOB1 world3).acs := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, hst, -, wB1, wB2, -⟩ := oracleFactsA
  have hcode : ((eOB world3).sta.withFork g).code = code := by
    simp only [Prod.mk.injEq] at hst; exact hst.2.2
  have w1 := (walk_transport hs hg (.avoid 0) codeTries okAny 278 (cOB0 world3)).trans wB1
  have w2 := (walk_transport hs hg (.avoid 0) codeTries okAny 1 (cOB1 world3)).trans wB2
  obtain ⟨hca, hall⟩ := leaf_frame_ok (.avoid 0) codeTries hcode okAny hag w1 w2
  exact ⟨(hall x hx).1, hca⟩

theorem oracleAcs_eq (a : Adr) : lookupA (cO3 world3).acs a = lookupA acs0 a := by
  obtain ⟨-, hk, hP, hC, hI⟩ := oracleFactsC
  refine lookupA_eq_of_keys (fun b hb => ?_) a
  have hk0 : acs0.map Prod.fst = [creator, proxyAddr, implAddr] := rfl
  rw [hk, hk0] at hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **Message 4, `set_oracle(0x00000000, 0x0)` through the clone**, on every covered fork,
from the world message 3 settles to (`world3`, described by `acs0` and `storInit`): it settles
to the closed machine `dO world3` with no error, 89,070 gas left and a refund counter of 4,800,
and that world keeps every account view and holds exactly the storage `storOracle`. -/
theorem oracle_run (g : Fork) (hg : CoveredFork g) (hW : WorldIs world3 acs0 storInit) :
    processMessage (oracleMsg g world3) = .ok (dO world3) ∧ (dO world3).error = none ∧
      (dO world3).gasLeft = 89070 ∧ (dO world3).refundCounter = 4800 ∧
      WorldIs (dO world3).state acs0 storOracle := by
  obtain ⟨he, hst, w1, p1, d1, hp, heB, -, hca, -, -, hdB, hr, w3, w4, hdT, hgas, hrc⟩ :=
    oracleFactsA
  obtain ⟨hcanon, -⟩ := oracleFactsC
  obtain ⟨hmsg, hca3⟩ := forwarder_root hg hW he hst w1 p1 d1 hp heB hca
    (fun hs hag => frameOB hg hs hag) hdB hr w3 w4 hdT
  refine ⟨hmsg, hdT, hgas, hrc, fun a => ?_, fun a k => ?_⟩
  · rw [← oracleAcs_eq a]; exact hca3.2.2.2 a
  · rw [hca3.2.2.1 a k, ← lookupS_canonS, hcanon]

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
