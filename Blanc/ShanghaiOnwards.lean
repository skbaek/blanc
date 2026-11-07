import Blanc.HistoricalFork

/-!
# The forks from Shanghai on

`ShanghaiOnwards` is a domain wider than `CoveredFork`: every fork the code on mainnet has run
under since a Shanghai-era activation. It keeps the facts a forward walk over legacy bytecode reads
(EIP-2929 access, the Prague gas numbers, no state gas, no sweep of touched accounts) and drops the
ones that begin later (transient storage, the calldata floor, EIP-7702 delegation).

`CoveredFork f` coerces to `ShanghaiOnwards f`, so a caller holding coverage can pass it unchanged
to a widened lemma. `CallEra` is the domain of the `CALL`-family step lemmas stated over the global
`accessDelegation`: from Shanghai on, with delegation live or the target holding no designator.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

open Jaune

/-- Forks at or after Shanghai, in activation order. -/
def ShanghaiOnwards (f : Fork) : Prop :=
  f ∈ [.shanghai, .cancun, .prague, .osaka, .bpo1, .bpo2]

instance : DecidablePred ShanghaiOnwards :=
  fun f => inferInstanceAs (Decidable (f ∈ [.shanghai, .cancun, .prague, .osaka, .bpo1, .bpo2]))

/-- Eliminate the domain into one case per fork. -/
theorem ShanghaiOnwards.cases {motive : Fork → Prop} {f : Fork}
    (h : ShanghaiOnwards f)
    (shanghai : motive .shanghai) (cancun : motive .cancun)
    (prague : motive .prague) (osaka : motive .osaka)
    (bpo1 : motive .bpo1) (bpo2 : motive .bpo2) : motive f := by
  unfold ShanghaiOnwards at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact shanghai
  · exact cancun
  · exact prague
  · exact osaka
  · exact bpo1
  · exact bpo2

/-- Modern coverage embeds in the domain. -/
theorem CoveredFork.shanghaiOnwards {f : Fork} : CoveredFork f → ShanghaiOnwards f := by
  cases f <;> decide

/-- A caller holding coverage passes it unchanged to a lemma widened to this domain. -/
instance {f : Fork} : Coe (CoveredFork f) (ShanghaiOnwards f) := ⟨CoveredFork.shanghaiOnwards⟩

/-- The domain embeds in the historical domain. -/
theorem ShanghaiOnwards.histFork {f : Fork} : ShanghaiOnwards f → HistFork f := by
  cases f <;> decide

/-- Transport along a fork equation. -/
theorem ShanghaiOnwards.of_eq {f1 f2 : Fork} (h : f1 = f2) (hf : ShanghaiOnwards f1) :
    ShanghaiOnwards f2 := by
  cases h; exact hf

/-- Amsterdam is outside the domain (the negative control at the top). -/
theorem ShanghaiOnwards.not_amsterdam : ¬ ShanghaiOnwards .amsterdam := by decide

/-- Paris is outside the domain (the negative control at the bottom). -/
theorem ShanghaiOnwards.not_paris : ¬ ShanghaiOnwards .paris := by decide

/-! ## Rule facts -/

theorem ShanghaiOnwards.stateGas_none {f : Fork} (h : ShanghaiOnwards f) :
    (Fork.ruleSet f).stateGas = none :=
  h.cases (motive := fun f => (Fork.ruleSet f).stateGas = none) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.bal_none {f : Fork} (h : ShanghaiOnwards f) :
    (Fork.ruleSet f).bal = none :=
  h.cases (motive := fun f => (Fork.ruleSet f).bal = none) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_stateGas_none {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.stateGas = none :=
  h.stateGas_none

theorem ShanghaiOnwards.rules_bal_none {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.bal = none :=
  h.bal_none

theorem ShanghaiOnwards.rules_access {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.access = .eip2929 :=
  h.cases (motive := fun f => (Fork.ruleSet f).access = .eip2929) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_push0 {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.op.push0 = true :=
  h.cases (motive := fun f => (Fork.ruleSet f).op.push0 = true) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_shifts {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.op.shifts = true :=
  h.cases (motive := fun f => (Fork.ruleSet f).op.shifts = true) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_chainId {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.op.chainId = true :=
  h.cases (motive := fun f => (Fork.ruleSet f).op.chainId = true) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_baseFee {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.op.baseFee = true :=
  h.cases (motive := fun f => (Fork.ruleSet f).op.baseFee = true) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_touchedSweep {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.settle.touchedSweep = false :=
  h.cases (motive := fun f => (Fork.ruleSet f).settle.touchedSweep = false) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_selfdestructRefund {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.settle.selfdestructRefund = 0 :=
  h.cases (motive := fun f => (Fork.ruleSet f).settle.selfdestructRefund = 0)
    rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_refundQuotient {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.settle.refundQuotient = 5 :=
  h.cases (motive := fun f => (Fork.ruleSet f).settle.refundQuotient = 5) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_dataNonZero {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.txr.dataNonZero = 16 :=
  h.cases (motive := fun f => (Fork.ruleSet f).txr.dataNonZero = 16) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_sstore {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.sstore = ⟨true, true⟩ :=
  h.cases (motive := fun f => (Fork.ruleSet f).sstore = ⟨true, true⟩) rfl rfl rfl rfl rfl rfl

/-- The whole domain uses the Prague gas schedule. -/
theorem BenvStat.gas_eq_prague_of_shanghaiOnwards {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.gas = pragueRules.gas :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas = pragueRules.gas) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_txBase {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.gas.txBase = 21000 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.txBase = 21000) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_floorTokenCost {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.gas.floorTokenCost = 10 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.floorTokenCost = 10) rfl rfl rfl rfl rfl rfl

theorem ShanghaiOnwards.rules_storageClearRefund {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.gas.storageClearRefund = 4800 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.storageClearRefund = 4800)
    rfl rfl rfl rfl rfl rfl

/-- The per-transaction gas cap is absent, or EIP-7825's `2 ^ 24` from Osaka. -/
theorem ShanghaiOnwards.rules_maxGas {s : BenvStat} (h : ShanghaiOnwards s.fork) :
    s.rules.tx.maxGas = none ∨ s.rules.tx.maxGas = some 16777216 :=
  h.cases (motive := fun f => (Fork.ruleSet f).tx.maxGas = none ∨
      (Fork.ruleSet f).tx.maxGas = some 16777216)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)

/-! ## The schedule: a timestamp from Shanghai on selects a fork from Shanghai on -/

/-- The last element a filter keeps lies at or after any kept element. -/
theorem mem_of_getLast?_filter_append_cons {α : Type _} {p : α → Bool} {l₁ l₂ : List α} {a b : α}
    (ha : p a = true) (h : ((l₁ ++ a :: l₂).filter p).getLast? = some b) : b ∈ a :: l₂ := by
  rw [List.filter_append, List.filter_cons_of_pos ha, List.getLast?_append_of_ne_nil _
    (List.cons_ne_nil _ _)] at h
  rcases List.mem_cons.mp (List.mem_of_getLast? h) with rfl | hb
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_of_mem_filter hb)

/-- A successful mainnet selection at or after Shanghai's timestamp is on the domain, whatever the
block number: every entry from Shanghai on is timestamp-activated and later in the schedule. -/
theorem mainnetChainConfig_shanghaiOnwards_of_timestamp_ge {number timestamp : Nat} {f : Fork}
    (selected : mainnetChainConfig.forkAt number timestamp = .ok f)
    (late : mainnetShanghaiTimestamp ≤ timestamp) : ShanghaiOnwards f := by
  have valid : mainnetChainConfig.validate = .ok () := by decide
  have someFork : mainnetChainConfig.forkAt? number timestamp = some f := by
    rw [ChainConfig.forkAt, valid] at selected
    cases lookup : mainnetChainConfig.forkAt? number timestamp with
    | none => simp only [lookup, Except.mapError, bind, Except.bind] at selected; cases selected
    | some g =>
      simp only [lookup, Except.mapError, bind, Except.bind, Except.ok.injEq] at selected
      rw [selected]
  unfold ChainConfig.forkAt? at someFork
  obtain ⟨activation, last, rfl⟩ := Option.map_eq_some_iff.mp someFork
  have member := mem_of_getLast?_filter_append_cons (α := ForkActivation)
    (l₁ := [.atBlock .byzantium mainnetByzantiumBlock,
      .atBlock .petersburg mainnetPetersburgBlock,
      .atBlock .istanbul mainnetIstanbulBlock,
      .atBlock .muirGlacier mainnetMuirGlacierBlock,
      .atBlock .berlin mainnetBerlinBlock,
      .atBlock .london mainnetLondonBlock,
      .atBlock .arrowGlacier mainnetArrowGlacierBlock,
      .atBlock .grayGlacier mainnetGrayGlacierBlock,
      .atBlock .paris mainnetParisBlock])
    (a := .atTime .shanghai mainnetShanghaiTimestamp)
    (l₂ := [.atTime .cancun mainnetCancunTimestamp,
      .atTime .prague mainnetPragueTimestamp,
      .atTime .osaka mainnetOsakaTimestamp,
      .atTime .bpo1 mainnetBpo1Timestamp,
      .atTime .bpo2 mainnetBpo2Timestamp])
    (p := (·.criterion.reached number timestamp))
    (by simp only [ForkActivation.atTime, ForkCriterion.reached, decide_eq_true_eq]; exact late)
    last
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The `CALL` family's delegation domain -/

/-- From Shanghai on, with EIP-7702 delegation live or the target holding no designator: where the
global `accessDelegation` answer `dp` is the one the selected rules give. -/
structure CallEra (f : Fork) (dp : Bool) : Prop where
  /-- The fork is in the domain. -/
  shanghai : ShanghaiOnwards f
  /-- Delegation is live, or the resolution found no designator. -/
  delegation : (Fork.ruleSet f).delegationEnabled = true ∨ dp = false

/-- Every covered fork has delegation live, so coverage gives the call domain at any `dp`. -/
theorem CoveredFork.callEra {f : Fork} (h : CoveredFork f) (dp : Bool) : CallEra f dp :=
  ⟨h, .inl (h.cases (motive := fun f => (Fork.ruleSet f).delegationEnabled = true)
    rfl rfl rfl rfl)⟩

/-- A caller holding coverage passes it unchanged to a `CALL`-family step lemma. -/
instance {f : Fork} {dp : Bool} : Coe (CoveredFork f) (CallEra f dp) := ⟨fun h => h.callEra dp⟩

/-- The domain at a target with no designator. -/
theorem ShanghaiOnwards.callEra {f : Fork} (h : ShanghaiOnwards f) : CallEra f false :=
  ⟨h, .inr rfl⟩

/-- On the call domain the selected rules' delegation resolution is the global one's answer. -/
theorem CallEra.rules_accessDelegation {s : BenvStat} {dp : Bool} {dadr : Adr} {code : ByteArray}
    {dgc : Nat} {d d1 : Devm} {a : Adr} (h : CallEra s.fork dp)
    (hdel : accessDelegation d a = ⟨dp, dadr, code, dgc, d1⟩) :
    s.rules.accessDelegation d a = ⟨dp, dadr, code, dgc, d1⟩ := by
  rcases Bool.eq_false_or_eq_true s.rules.delegationEnabled with enabled | disabled
  · rw [ForkRules.accessDelegation_enabled enabled, BenvStat.gas_eq_prague_of_shanghaiOnwards
      h.shanghai]
    exact (accessDelegation_eq d a).trans hdel
  · have hdp : dp = false := h.delegation.resolve_left (fun e => by
      change s.rules.delegationEnabled = true at e
      rw [disabled] at e
      cases e)
    subst hdp
    rw [ForkRules.accessDelegation_disabled disabled]
    unfold accessDelegation at hdel
    cases hd : getDelegatedCodeAddress (d.state.getCode a) with
    | none =>
      simp only [hd] at hdel
      exact hdel
    | some x =>
      simp only [hd] at hdel
      cases hdel

end Blanc
