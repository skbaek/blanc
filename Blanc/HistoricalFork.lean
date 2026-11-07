import Blanc.Semantics

namespace Blanc

open Jaune

/-- The two rule facts used by fork-neutral historical extraction. They do
not assert opcode availability, gas prices, settlement or optional passes. -/
structure NeutralFork (f : Fork) : Prop where
  stateGas : f.ruleSet.stateGas = none
  bal : f.ruleSet.bal = none

/-- The accepted historical domain, including synthetic Constantinople and
excluding Amsterdam. This does not widen the modern `coveredForks`. -/
def histForks : List Fork :=
  [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier, .berlin,
   .london, .arrowGlacier, .grayGlacier, .paris, .shanghai, .cancun,
   .prague, .osaka, .bpo1, .bpo2]

/-- Membership in the historical extraction domain. -/
def HistFork (f : Fork) : Prop := f ∈ histForks

instance : DecidablePred HistFork :=
  fun f => inferInstanceAs (Decidable (f ∈ histForks))

/-- Historical extraction does not use state gas. -/
theorem HistFork.stateGas_none {f : Fork} :
    HistFork f → f.ruleSet.stateGas = none := by
  cases f <;> decide

/-- Historical forks in this domain do not require a block access list. -/
theorem HistFork.bal_none {f : Fork} :
    HistFork f → f.ruleSet.bal = none := by
  cases f <;> decide

/-- Historical domain membership supplies exactly the neutral rule facts. -/
theorem HistFork.neutral {f : Fork} (h : HistFork f) : NeutralFork f :=
  ⟨h.stateGas_none, h.bal_none⟩

/-- A request-enabled historical selection is in the existing modern domain.
The earlier forks disable requests, rather than carrying invented calls. -/
theorem HistFork.requests_covered {f : Fork} :
    HistFork f → f.ruleSet.header.requestsHash = true → CoveredFork f := by
  cases f <;> decide

/-- Modern coverage embeds in the separate historical domain. -/
theorem CoveredFork.histFork {f : Fork} : CoveredFork f → HistFork f := by
  cases f <;> decide

/-- Amsterdam remains outside the historical extraction domain. -/
theorem HistFork.not_amsterdam : ¬ HistFork .amsterdam := by decide

/-! Rule facts under Amsterdam, stated beside `CoveredFork`'s and leaving it as it is: a walk that
runs under Amsterdam takes `s.fork = .amsterdam` and reads the rule record through these. -/

/-- `.amsterdam` resolves to `amsterdamRules` in the record the machine reads. -/
theorem amsterdam_rules {s : BenvStat} (h : s.fork = .amsterdam) : s.rules = amsterdamRules := by
  show Fork.ruleSet s.fork = _
  rw [h]
  rfl

theorem amsterdam_stateGas {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.stateGas = some amsterdamStateGasRules := by
  rw [amsterdam_rules h]
  rfl

theorem amsterdam_access {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.access = .eip2929 := by
  rw [amsterdam_rules h]
  rfl

theorem amsterdam_push0 {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.op.push0 = true := by
  rw [amsterdam_rules h]
  rfl

theorem amsterdam_shifts {s : BenvStat} (h : s.fork = .amsterdam) :
    s.rules.op.shifts = true := by
  rw [amsterdam_rules h]
  rfl

/-- Every successful mainnet selection belongs to the historical domain.
Both schedule coordinates are retained; a lookup below its floor may fail. -/
theorem mainnet_histFork {number timestamp : Nat} {f : Fork}
    (h : mainnetChainConfig.forkAt number timestamp = .ok f) : HistFork f := by
  have hmem := Jaune.ChainConfig.forkAt_mem h
  have historical : ∀ f,
      f ∈ mainnetChainConfig.activations.map (·.fork) → HistFork f := by
    intro f
    cases f <;> decide
  exact historical f hmem

end Blanc
