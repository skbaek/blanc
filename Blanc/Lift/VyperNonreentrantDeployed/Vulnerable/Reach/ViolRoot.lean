import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRootRun

/-!
# V− P2, F0/F1 entry: the root frame and its forwarder child

`RootEntryFacts`: from the message's start configuration `cR0` (static machine `S0`),
the root's `CALL` (33 steps), the outer forwarder, its `DELEGATECALL` into F2, and F2's
entered start configuration `c2` (which agrees, for `RemoveFrame` to consume in piece 3).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- F0's `CALL` prep under any covered fork. -/
theorem cpR_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    callPrep ((sR.withOrig O).withFork g) (cR O tS tA m w) =
      some ((cpR O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (sR.withOrig O).benvStat.fork := by
    rw [sR_orig_fork O]
    exact CoveredFork.prague
  show callPrep ((sR.withOrig O).withFork g) _ = _
  rw [callPrep_withFork hF hg, cpR_eq O tS tA m w]
  rfl

/-- The outer forwarder's entry under any covered fork. -/
theorem e1R_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    frameEnterS (((cpR O tS tA m w).withFork g).f) (cR O tS tA m w).acs =
      .run ((e1 O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (sR.withOrig O).benvStat.fork := by
    rw [sR_orig_fork O]
    exact CoveredFork.prague
  show frameEnterS ((cpR O tS tA m w).f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat hF hg (callPrep_stat (cpR_eq O tS tA m w))
    (cpR_neutral O tS tA m w), e1_eq O tS tA m w]
  rfl

/-- The outer forwarder's 11-step prefix under any covered fork. -/
theorem e1'11_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    stepN 11 ((e1 O tS tA m w).withFork g) =
      some ((e1'11 O tS tA m w).withFork g) := by
  intro _ O tS tA m w hg
  exact stepN_withFork hg (e1_fork O tS tA m w).1 (e1_fork O tS tA m w).2
    (e1'11_eq O tS tA m w)

/-- F1's `DELEGATECALL` prep and F2's entry under any covered fork. -/
theorem cpF2_e2_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    dcallPrep ((e1'11 O tS tA m w).sta.withFork g)
        ((e1'11 O tS tA m w).dyna) (cpR O tS tA m w).adrs
        (acs1R O tS tA m w) = some ((cpF2 O tS tA m w).withFork g) ∧
      frameEnterS (((cpF2 O tS tA m w).withFork g).f) (acs1R O tS tA m w) =
        .run ((e2 O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (e1'11 O tS tA m w).sta.benvStat.fork := by
    rw [stepN_sta (e1'11_eq O tS tA m w), (e1_fork O tS tA m w).1]
    exact CoveredFork.prague
  exact dcallSpawn_withFork hF hg (cpF2_eq O tS tA m w) (cpF2_neutral O tS tA m w)
    (e2_eq O tS tA m w)

/-- F2's entry addresses and accounts, from the prep specs. -/
theorem chain1_of (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World)
    (hAgreeR : Agree (cR O tS tA m w)) :
    (∀ a, a ∈ (e1'11 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpR O tS tA m w).adrs) ∧
    AcctAgree (e1'11 O tS tA m w).dyna.state (acs1R O tS tA m w) := by
  have hcsC := callPrep_spec (cpR_eq O tS tA m w) hAgreeR.2.1 hAgreeR.2.2.2
  obtain ⟨cstep, cpa, cpk, ccr, cia, cik, csg, cst8⟩ := hcsC
  obtain ⟨benv1, hb1, he1⟩ := frameEnterS_run (e1_eq O tS tA m w)
  have hC1pre : AcctAgree (cpR O tS tA m w).f.inner.benv.state
      (cR O tS tA m w).acs := by
    rw [cst8]
    exact hAgreeR.2.2.2
  have hC1 : AcctAgree benv1.state (acs1R O tS tA m w) :=
    acctAgree_transfer hC1pre hb1
  have hA4 : ∀ a, a ∈ (e1'11 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpR O tS tA m w).adrs := by
    intro a
    rw [e1'11_acc O tS tA m w, e1_entry_acc O tS tA m w, cia, cpa]
  have hC4' : AcctAgree (e1'11 O tS tA m w).dyna.state (acs1R O tS tA m w) := by
    rw [e1'11_state O tS tA m w, he1]
    exact hC1
  exact ⟨hA4, hC4'⟩

/-- F2's start configuration agrees, from F0's `CALL` agreement: keys and addresses
by the prep specs, storage and accounts across F1's value transfer. -/
theorem c2R_agree : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), Agree (cR O tS tA m w) → Agree (c2 O tS tA m w) := by
  intro O tS tA m w hA
  have hcsC := callPrep_spec (cpR_eq O tS tA m w) hA.2.1 hA.2.2.2
  obtain ⟨cstep, cpa, cpk, ccr, cia, cik, csg, cst8⟩ := hcsC
  obtain ⟨benv1, hb1, he1⟩ := frameEnterS_run (e1_eq O tS tA m w)
  have hC1pre : AcctAgree (cpR O tS tA m w).f.inner.benv.state
      (cR O tS tA m w).acs := by
    rw [cst8]
    exact hA.2.2.2
  have hC1 : AcctAgree benv1.state (acs1R O tS tA m w) :=
    acctAgree_transfer hC1pre hb1
  have hA4 : ∀ a, a ∈ (e1'11 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpR O tS tA m w).adrs := by
    intro a
    rw [e1'11_acc O tS tA m w, e1_entry_acc O tS tA m w, cia, cpa]
  have hC4' : AcctAgree (e1'11 O tS tA m w).dyna.state (acs1R O tS tA m w) := by
    rw [e1'11_state O tS tA m w, he1]
    exact hC1
  have hdc := dcallPrep_spec (cpF2_eq O tS tA m w) hA4 hC4'
  obtain ⟨dstep, dpa, dpk, dcr, dia, dik, dsg, dst8, dst9⟩ := hdc
  refine frameStart_agree (Vulnerable.t_0000_c0) (e2_eq O tS tA m w) ?hK ?hA' ?hS ?hC
  · intro x
    rw [dik, dpk, e1'11_keys O tS tA m w, e1_entry_keys O tS tA m w, cik, cpk]
    exact hA.1 x
  · intro a
    rw [dia, dpa]
  · intro a k
    rw [dst8, e1'11_state O tS tA m w, he1]
    show storOf benv1.state a k = lookupS (cR O tS tA m w).stor a k
    have hB : benvAfterTransferB (cpR O tS tA m w).f.inner = .ok benv1 := by
      rw [benvAfterTransfer_eq_S hC1pre]
      exact hb1
    have hstor := benvAfterTransferB_stor hB a k
    rw [hstor, cst8]
    exact hA.2.2.1 a k
  · rw [dst8, e1'11_state O tS tA m w, he1]
    exact hC1

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
