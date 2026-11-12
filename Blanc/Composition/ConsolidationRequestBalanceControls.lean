import Blanc.Composition.Corpus.Freeze.ConsolidationJoint
import JauneConsensus.Facts.AnchorInvControls
import Blanc.ConcreteRun

namespace Blanc.Composition.ConsolidationRequestBalanceControls

open Jaune JauneConsensus Blanc
open Blanc.Corpus.Freeze.ConsolidationJoint

/-- The frozen `pendingList` is Jaune's `pendingConsolidationsList`. -/
theorem pendingList_eq {P : Preset} {f : CFork} (st : BeaconState P f) :
    pendingList st = Facts.pendingConsolidationsList st := rfl

/-- Positive derivation: a guarded `Transfers` plus distinctness gives the unguarded transfer. -/
theorem unguarded_of_transfers {P : Preset} {f : CFork} {u u' : BeaconState P f}
    {pc : PendingConsolidation} {source : Validator}
    (transfers : Transfers u u' pc source) (distinct : pc.source_index ≠ pc.target_index) :
    UnguardedTransfers u u' pc source := by
  obtain ⟨sb, hsb, hval, hother, hmoved⟩ := transfers
  obtain ⟨tb, sb', tb', htb, hsb', htb', hs, ht⟩ := hmoved distinct
  exact ⟨sb, tb, sb', tb', hsb, htb, hsb', htb', hval, hother, hs, ht⟩

/-- **C-S9 balance negative control.** -/
theorem c_s9_balance_control : C_S9_balance_control := by
  refine ⟨fun transfers distinct => unguarded_of_transfers transfers distinct, ?_⟩
  obtain ⟨_, _, _, w', hrun, hpc, hbal, hnot, hnot'⟩ :=
    Facts.pendingConsolidationsDistinct_negative_control
  refine ⟨Facts.s_pc_self, w', ⟨U64.zero, U64.zero⟩, Facts.ctrlValidator, U64.zero, U64.one,
    U64.lit 32000000000, U64.lit 32000000000, ?_, rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_, hrun, hpc, hbal,
    rfl, ?_, ?_, ?_⟩
  · rw [pendingList_eq, Facts.pendingConsolidationsList_eq_get rfl]; rfl
  · rfl
  · rfl
  · rfl
  · decide
  · rfl
  · decide
  · exact fun h => hnot ⟨_, hbal, h⟩
  · exact fun h => hnot' ⟨_, _, rfl, hbal, h⟩
  · intro ⟨sb, tb, sb', tb', h1, h2, h3, h4, _, _, e1, e2⟩
    have hsb : sb = U64.lit 32000000000 := Option.some.inj (h1.symm.trans rfl)
    have htb : tb = U64.lit 32000000000 := Option.some.inj (h2.symm.trans rfl)
    have hsb' : sb' = tb' := Option.some.inj (h3.symm.trans h4)
    have hm : min (U64.lit 32000000000).toNat Facts.ctrlValidator.effective_balance.toNat =
        32000000000 := rfl
    have hl : (U64.lit 32000000000).toNat = 32000000000 := rfl
    subst hsb htb hsb'
    rw [hm, hl] at e1 e2
    omega

end Blanc.Composition.ConsolidationRequestBalanceControls
