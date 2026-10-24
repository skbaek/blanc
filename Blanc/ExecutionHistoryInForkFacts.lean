import Blanc.HistoricalFork

/-!
# Fork-era facts for historical extraction

Schedule properties of the historical domain (`Blanc/HistoricalFork.lean`),
proved over `histForks` by decision (the `HistFork.dataNonZero_ge` pattern in
`Blanc/ExecutionStagedFrameEnv.lean`): EIP-2929 access from Berlin on, the
`0x02` precompile on every historical fork, disabled EIP-7702 delegation
before Prague, and the system-call flags by era (no system stage before
Cancun, beacon roots only on Cancun, all four from Prague).

Contract-neutral: no contract name in any statement. These are the per-fork
premises the historical environment facts discharge by decision; nothing here
assumes coverage, delegation, or any access schedule.
-/

namespace Blanc

open Jaune

/-- Forks at or after Berlin, in activation order. -/
def BerlinOnwards (f : Fork) : Prop :=
  f ∈ [.berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai,
    .cancun, .prague, .osaka, .bpo1, .bpo2]

instance : DecidablePred BerlinOnwards :=
  fun f => inferInstanceAs (Decidable (f ∈
    [.berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai,
      .cancun, .prague, .osaka, .bpo1, .bpo2]))

/-- Forks before Prague, in activation order. -/
def PrePrague (f : Fork) : Prop :=
  f ∈ [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier,
    .berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai, .cancun]

instance : DecidablePred PrePrague :=
  fun f => inferInstanceAs (Decidable (f ∈
    [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier,
      .berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai,
      .cancun]))

/-- Forks before Cancun, in activation order. -/
def PreCancun (f : Fork) : Prop :=
  f ∈ [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier,
    .berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai]

instance : DecidablePred PreCancun :=
  fun f => inferInstanceAs (Decidable (f ∈
    [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier,
      .berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai]))

/-- Forks at or after Prague, in activation order. -/
def PragueOnwards (f : Fork) : Prop :=
  f ∈ [.prague, .osaka, .bpo1, .bpo2]

instance : DecidablePred PragueOnwards :=
  fun f => inferInstanceAs (Decidable (f ∈ [.prague, .osaka, .bpo1, .bpo2]))

/-- Every historical fork from Berlin on uses EIP-2929 access. -/
theorem HistFork.access_eip2929_of_berlinOnwards {f : Fork}
    (h : HistFork f) (hb : BerlinOnwards f) :
    (Fork.ruleSet f).access = .eip2929 := by
  revert h hb
  cases f <;> decide

/-- The `0x02` precompile is active on every historical fork. -/
theorem HistFork.two_mem_precompiles {f : Fork} (h : HistFork f) :
    (2 : Adr) ∈ (Fork.ruleSet f).precompiles := by
  revert h
  cases f <;> decide

/-- EIP-7702 delegation is disabled on every historical fork before Prague. -/
theorem HistFork.delegationDisabled_of_prePrague {f : Fork}
    (h : HistFork f) (hp : PrePrague f) :
    (Fork.ruleSet f).delegationEnabled = false := by
  revert h hp
  cases f <;> decide

/-- No beacon-roots stage before Cancun. -/
theorem HistFork.sys_beaconRoots_false_of_preCancun {f : Fork}
    (h : HistFork f) (hc : PreCancun f) :
    (Fork.ruleSet f).sys.beaconRoots = false := by
  revert h hc
  cases f <;> decide

/-- The beacon-roots stage runs on Cancun. -/
theorem HistFork.sys_beaconRoots_true_of_cancun {f : Fork}
    (h : HistFork f) (hc : f = .cancun) :
    (Fork.ruleSet f).sys.beaconRoots = true := by
  revert h hc
  cases f <;> decide

/-- The beacon-roots stage runs from Prague on. -/
theorem HistFork.sys_beaconRoots_true_of_pragueOnwards {f : Fork}
    (h : HistFork f) (hp : PragueOnwards f) :
    (Fork.ruleSet f).sys.beaconRoots = true := by
  revert h hp
  cases f <;> decide

/-- No history-storage stage before Prague. -/
theorem HistFork.sys_historyStorage_false_of_prePrague {f : Fork}
    (h : HistFork f) (hp : PrePrague f) :
    (Fork.ruleSet f).sys.historyStorage = false := by
  revert h hp
  cases f <;> decide

/-- The history-storage stage runs from Prague on. -/
theorem HistFork.sys_historyStorage_true_of_pragueOnwards {f : Fork}
    (h : HistFork f) (hp : PragueOnwards f) :
    (Fork.ruleSet f).sys.historyStorage = true := by
  revert h hp
  cases f <;> decide

/-- No request stage before Prague. -/
theorem HistFork.header_requestsHash_false_of_prePrague {f : Fork}
    (h : HistFork f) (hp : PrePrague f) :
    (Fork.ruleSet f).header.requestsHash = false := by
  revert h hp
  cases f <;> decide

/-- The request stage runs from Prague on. -/
theorem HistFork.header_requestsHash_true_of_pragueOnwards {f : Fork}
    (h : HistFork f) (hp : PragueOnwards f) :
    (Fork.ruleSet f).header.requestsHash = true := by
  revert h hp
  cases f <;> decide

/-- Forks at or after Cancun, in activation order. -/
def CancunOnwards (f : Fork) : Prop :=
  f ∈ [.cancun, .prague, .osaka, .bpo1, .bpo2]

instance : DecidablePred CancunOnwards :=
  fun f => inferInstanceAs (Decidable (f ∈
    [.cancun, .prague, .osaka, .bpo1, .bpo2]))

/-- Every historical fork is pre-Cancun, Cancun, or Prague-onwards. -/
theorem HistFork.preCancun_cancun_pragueOnwards {f : Fork} (h : HistFork f) :
    PreCancun f ∨ f = .cancun ∨ PragueOnwards f := by
  revert h
  cases f <;> decide

/-- Every historical fork is pre-Cancun or Cancun-onwards. -/
theorem HistFork.preCancun_cancunOnwards {f : Fork} (h : HistFork f) :
    PreCancun f ∨ CancunOnwards f := by
  revert h
  cases f <;> decide

/-- A Prague-onwards historical fork is in the modern covered domain
(Cancun itself is not covered). -/
theorem HistFork.pragueOnwards_covered {f : Fork}
    (h : HistFork f) (hp : PragueOnwards f) : CoveredFork f := by
  revert h hp
  cases f <;> decide

/-- EIP-6780 self-destruct scoping holds on every Cancun-onwards fork. -/
theorem HistFork.selfdestructOnlyCreated_of_cancunOnwards {f : Fork}
    (h : HistFork f) (hc : CancunOnwards f) :
    (Fork.ruleSet f).settle.selfdestructOnlyCreated = true := by
  revert h hc
  cases f <;> decide

/-- Cancun-onwards forks carry the EIP-3529 refund quotient. -/
theorem HistFork.refundQuotient_five_of_cancunOnwards {f : Fork}
    (h : HistFork f) (hc : CancunOnwards f) :
    (Fork.ruleSet f).settle.refundQuotient = 5 := by
  revert h hc
  cases f <;> decide

/-- Cancun-onwards forks do not sweep touched accounts at settlement. -/
theorem HistFork.touchedSweep_false_of_cancunOnwards {f : Fork}
    (h : HistFork f) (hc : CancunOnwards f) :
    (Fork.ruleSet f).settle.touchedSweep = false := by
  revert h hc
  cases f <;> decide

/-- Cancun itself does not hash requests into the header. -/
theorem HistFork.header_requestsHash_false_of_cancun {f : Fork}
    (h : HistFork f) (hc : f = .cancun) :
    (Fork.ruleSet f).header.requestsHash = false := by
  revert h hc
  cases f <;> decide

/-- A pre-Cancun fork is pre-Prague. -/
theorem PreCancun.toPrePrague {f : Fork} (h : PreCancun f) : PrePrague f := by
  revert h
  cases f <;> decide

end Blanc
