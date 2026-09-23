import Blanc.Ladder

/-!
Controls for the fork-coverage restriction of 2026-09-23 (user decision
`consumability-historical-forks-20260922`).  Blanc consumes a Jaune pin whose
`Fork` has Amsterdam semantics, and every statement that would otherwise
acquire Amsterdam cases is restricted by `CoveredFork`.  The covered forks are
exactly Prague, Osaka, BPO1 and BPO2, the four forks the previous pin defined,
so a restricted statement keeps its whole historical fork index.  Amsterdam is
not covered, and coverage of it is never inferred.

The file is elaborated by `scripts/check-claims.sh`.  It holds:

* positive witnesses: each historically covered fork is covered, in both the
  bare form and the frame-premise form (`CoveredFork sevm.benvStat.fork`) that
  restricted frame theorems take;
* the schedule-premise form (`∀ t f, cfg.forkAt t = .ok f → CoveredFork f`)
  discharged for Jaune's mainnet schedule by `mainnetChainConfig_covered`, and
  consumed by the configured-chain frame-to-chain ladder at that schedule;
* the Amsterdam-negative control, in both forms;
* an exact pin of the covered list.

The witnesses are deliberately not in `scripts/AxiomCheck.lean`, so the
published audited-theorem count is unchanged (master decision E8-A).

Bite, shown once in a disposable mutation worktree and recorded in the Plans
B2 evidence: removing `.osaka` from `Blanc.coveredForks` breaks the Osaka
witnesses, `mainnetChainConfig_covered` and the list pin; adding `.amsterdam`
breaks both negative controls and the list pin.  Restoring the list restores
green.
-/

namespace Blanc.CoveredForkControls

open Jaune Blanc

/-! ### Positive witnesses: every historically covered fork survives. -/

theorem prague_covered : CoveredFork .prague := CoveredFork.prague
theorem osaka_covered : CoveredFork .osaka := CoveredFork.osaka
theorem bpo1_covered : CoveredFork .bpo1 := CoveredFork.bpo1
theorem bpo2_covered : CoveredFork .bpo2 := CoveredFork.bpo2

/-- The frame premise every restricted frame theorem takes is dischargeable at
a frame running any of the four covered forks. -/
theorem frame_covered {s : Sevm}
    (h : s.benvStat.fork = .prague ∨ s.benvStat.fork = .osaka ∨
      s.benvStat.fork = .bpo1 ∨ s.benvStat.fork = .bpo2) :
    CoveredFork s.benvStat.fork := by
  rcases h with h | h | h | h <;> rw [h]
  · exact CoveredFork.prague
  · exact CoveredFork.osaka
  · exact CoveredFork.bpo1
  · exact CoveredFork.bpo2

/-! ### The schedule premise at Jaune's mainnet schedule. -/

/-- Mainnet's activations are exactly the four covered forks, so the
configured-chain premise holds there without assumption. -/
theorem mainnet_schedule_covered :
    ∀ t f, mainnetChainConfig.forkAt t = .ok f → CoveredFork f :=
  mainnetChainConfig_covered

/-- End to end: the configured-chain ladder, restricted by the schedule
premise, applies to every reachable mainnet chain with the premise discharged,
not assumed. -/
theorem mainnet_chain_preserves_inv (c : ContractSpec) (wa : Adr)
    (hp : c.Preserves wa) (ch ch' : BlockChain)
    (h_reach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (h_inv : c.StateInv wa ch.state) :
    c.StateInv wa ch'.state :=
  c.chainUsing_preserves_inv wa hp mainnetChainConfig ch ch' h_reach h_inv
    mainnetChainConfig_covered

/-! ### Amsterdam-negative control: no restricted statement reaches Amsterdam. -/

theorem amsterdam_not_covered : ¬ CoveredFork .amsterdam :=
  CoveredFork.not_amsterdam

theorem amsterdam_frame_not_covered {s : Sevm}
    (h : s.benvStat.fork = .amsterdam) : ¬ CoveredFork s.benvStat.fork := by
  rw [h]
  exact CoveredFork.not_amsterdam

/-! ### The covered set, pinned exactly: a fifth Jaune fork is never inferred
covered, and dropping one of the four fails here. -/

theorem coveredForks_pinned :
    coveredForks = [.prague, .osaka, .bpo1, .bpo2] := rfl

end Blanc.CoveredForkControls
