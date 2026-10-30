import Blanc.ExecutionHistoryInSystemEnvironment
import Blanc.ExecutionHistoryInAppend

/-! Actual schedule intervals and opening-code producers for historical seams.
Fork indices here compare selections of the same validated schedule; they do not
replace rule facts inside execution. No installed code is required before Cancun. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- A property of each actual selected fork in a retained block spine. -/
def ConfiguredHistoryTraceIn.ForksSatisfy
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint : BlockChain} (G : Fork → Prop) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.ForksSatisfy G ∧ G block.fork

theorem ConfiguredHistoryTraceIn.ForksSatisfy.mono
    {F G H : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTraceIn F cfg checkpoint future}
    (holds : trace.ForksSatisfy G) (implies : ∀ f, G f → H f) :
    trace.ForksSatisfy H := by
  induction trace with
  | refl => trivial
  | step prior block ih => exact ⟨ih holds.1, implies _ holds.2⟩

/-- The actual final tip has a selected fork no earlier than the actual opening tip. -/
theorem ConfiguredHistoryTraceIn.tip_fork_mono
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {start : Block} {lower : Fork}
    (startTip : checkpoint.blocks.getLast? = some start)
    (startFork : cfg.forkAt start.header.number start.header.timestamp = .ok lower) :
    ∃ finish upper, future.blocks.getLast? = some finish ∧
      cfg.forkAt finish.header.number finish.header.timestamp = .ok upper ∧
      lower.index ≤ upper.index := by
  induction trace with
  | refl => exact ⟨start, lower, startTip, startFork, Nat.le_refl _⟩
  | step prior block ih =>
      obtain ⟨tip, fork, tipLast, tipFork, lowerLe⟩ := ih
      obtain ⟨selected, selectedAt, forkLe, -⟩ :=
        stateTransitionUsing_fork_mono tipLast tipFork block.transition
      have same : selected = block.fork := Except.ok.inj (selectedAt.symm.trans block.forkAt)
      subst selected
      refine ⟨block.block, block.fork, ?_, block.forkAt, lowerLe.trans forkLe⟩
      exact (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
        (appendBlock_getLast? _ _)

/-- Actual transitions bound every selected fork by the two endpoint-tip selections. -/
theorem ConfiguredHistoryTraceIn.forksSatisfy_between
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {start finish : Block} {lower upper : Fork}
    (startTip : checkpoint.blocks.getLast? = some start)
    (startFork : cfg.forkAt start.header.number start.header.timestamp = .ok lower)
    (finishTip : future.blocks.getLast? = some finish)
    (finishFork : cfg.forkAt finish.header.number finish.header.timestamp = .ok upper) :
    trace.ForksSatisfy (fun f => lower.index ≤ f.index ∧ f.index ≤ upper.index) := by
  induction trace generalizing finish upper with
  | refl => trivial
  | step prior block ih =>
      have last := (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
        (appendBlock_getLast? _ _)
      have sameBlock : finish = block.block := Option.some.inj (finishTip.symm.trans last)
      subst finish
      have sameFork : upper = block.fork := Except.ok.inj (finishFork.symm.trans block.forkAt)
      subst upper
      obtain ⟨tip, fork, tipLast, tipFork, lowerLe⟩ := prior.tip_fork_mono startTip startFork
      obtain ⟨selected, selectedAt, forkLe, -⟩ :=
        stateTransitionUsing_fork_mono tipLast tipFork block.transition
      have same : selected = block.fork := Except.ok.inj (selectedAt.symm.trans block.forkAt)
      subst selected
      have priorFacts := ih tipLast tipFork
      exact ⟨priorFacts.mono (fun _ h => ⟨h.1, h.2.trans forkLe⟩),
        lowerLe.trans forkLe, Nat.le_refl _⟩

/-- Pre-Cancun blocks have no opening installation obligations. -/
theorem ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_preCancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy PreCancun) : trace.SystemCodeAtOpenings := by
  induction trace with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih forks.1, SystemCodeInstalledAt.of_preCancun _ block.forkIn forks.2⟩

/-- The actual Cancun spine obtains every opening from one initial beacon-code anchor. -/
theorem ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_cancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy (fun f => f = .cancun))
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress)
    (installed : checkpoint.state.getCode beaconRootsAddress = beaconRootsCode) :
    trace.SystemCodeAtOpenings ∧ future.state.getCode beaconRootsAddress = beaconRootsCode := by
  induction trace with
  | refl => exact ⟨trivial, installed⟩
  | step prior block ih =>
      obtain ⟨priorOpenings, priorCode⟩ := ih forks.1 (fun root member => avoid root (by
        simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
        exact Or.inl member))
      have opening : block.SystemCodeAtOpening := by
        intro p member
        rw [HistFork.installedAt_beacon_of_cancun block.forkIn forks.2] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst p
        exact priorCode
      have facts := systemContracts_facts _ beaconRoots_mem_systemContracts
      have keep := block.codeAt_keep_of_cancunOnwards BodyStageCapabilities.historical
        block.forkIn (by rw [forks.2]; decide)
        (Or.inl (by rw [forks.2]; rfl))
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) priorCode facts.2.2 facts.2.1
      exact ⟨⟨priorOpenings, opening⟩, keep⟩

/-- Opening installation producers compose along the same retained append. -/
theorem ConfiguredHistoryTraceIn.SystemCodeAtOpenings_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).SystemCodeAtOpenings ↔
      left.SystemCodeAtOpenings ∧ right.SystemCodeAtOpenings := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, ih, and_assoc]

/-- Fork properties split across the same retained append. -/
theorem ConfiguredHistoryTraceIn.ForksSatisfy_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain} (G : Fork → Prop)
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).ForksSatisfy G ↔ left.ForksSatisfy G ∧ right.ForksSatisfy G := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, ih, and_assoc]

/-- Installed-target frame exclusions split across the same retained append. -/
theorem ConfiguredHistoryTraceIn.InstalledNoFrame_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).InstalledNoFrame ↔ left.InstalledNoFrame ∧ right.InstalledNoFrame := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, InstalledNoFrame, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, InstalledNoFrame, ih, and_assoc]

/-- A pre-Prague spine needs no authority exclusion: the gated form holds outright. -/
theorem ConfiguredHistoryTraceIn.pragueNoAuthorityAt_of_prePrague
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (forks : trace.ForksSatisfy PrePrague) (a : Adr) : trace.PragueNoAuthorityAt a := by
  induction trace with
  | refl => trivial
  | step prior block ih => exact ⟨ih forks.1, fun notPre => (notPre forks.2).elim⟩

/-- On a Cancun block the installed-target exclusion is exactly the beacon-roots one. -/
theorem ConfiguredBlockTraceIn.beaconNoFrame_of_cancun
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) (fork : block.fork = .cancun)
    (avoid : block.InstalledNoFrame) :
    ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress :=
  avoid (beaconRootsAddress, beaconRootsCode) (by
    rw [HistFork.installedAt_beacon_of_cancun block.forkIn fork]
    exact List.mem_cons_self)

/-- Over a Cancun spine the installed-target exclusion is exactly the beacon-roots one. -/
theorem ConfiguredHistoryTraceIn.beaconNoFrame_of_cancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy (fun f => f = .cancun)) (avoid : trace.InstalledNoFrame) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress := by
  induction trace with
  | refl => intro root member; simp only [ConfiguredHistoryTraceIn.rawFrames,
      List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih forks.1 avoid.1 root member
      · exact block.beaconNoFrame_of_cancun forks.2 avoid.2 root member

/-- Actual authorization scopes split across the same retained append. -/
theorem ConfiguredHistoryTraceIn.NoAuthorityAt_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c)
    (address : Adr) :
    (left.append right).NoAuthorityAt address ↔
      left.NoAuthorityAt address ∧ right.NoAuthorityAt address := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, NoAuthorityAt, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, NoAuthorityAt, ih, and_assoc]

end Blanc.ExecutionTrace
