import Blanc.ExecutionMidHistoryInCallerExclusion
import Blanc.ExecutionHistoryInSystemCodeKeep

/-!
The residual beacon-installation condition of a Cancun mid history follows from
one actual checkpoint and CREATE avoidance, by the existing code-preservation chain.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual suffix after a Cancun transaction preserves nonempty ordinary
code at an account avoided by entered CREATE frames. -/
theorem ConfiguredBlockTraceIn.tail_codeAt_keep_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {a : Adr} {code : ByteArray}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (fork : block.fork = .cancun)
    (avoid : ∀ root ∈ (MidHistoryTraceIn.tail block cut).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (installed : cut.afterBenv.state.getCode a = code)
    (nonempty : code.toList ≠ []) (ordinary : ¬ isValidDelegation code) :
    post.state.getCode a = code := by
  have requests := block.requests_rawFrames_empty_cancun fork
  simp only [MidHistoryTraceIn.rawFrames, requests, List.append_nil] at avoid
  have cutFork : cut.afterBenv.stat.fork = .cancun := by
    rw [block.txSplit_stat cut]
    exact fork
  have rules : cut.afterBenv.stat.rules = Fork.ruleSet .cancun := by
    change Fork.ruleSet cut.afterBenv.stat.fork = _
    rw [cutFork]
  have finalTx := cut.after.codeAt_keep_noStateGas (benv := cut.afterBenv)
    (by rw [rules]; rfl) (by rw [rules]; rfl)
    (by change cut.afterBenv.stat.rules.settle.refundQuotient = 5; rw [rules]; rfl)
    (by change cut.afterBenv.stat.rules.settle.touchedSweep = false; rw [rules]; rfl)
    (Or.inl (by rw [rules]; rfl)) avoid
    (by rw [installed]; exact nonempty) (by rw [installed]; exact ordinary)
    (block.txSplit_notCreated cut a)
  have afterTx := block.bodyTrace.afterTransactions_codeAt_noStateGas
    (a := a) (by
      rw [block.bodyTrace.transactions.stat_eq]
      change block.fork.ruleSet.stateGas = none
      rw [fork]
      rfl) (by intro root member; rw [requests] at member; cases member)
  rw [block.postEq]
  exact afterTx.trans (finalTx.trans installed)

/-- A whole Cancun block preserves nonempty ordinary installed code under
actual CREATE avoidance; every schedule fact comes from the selected fork. -/
theorem ConfiguredBlockTraceIn.codeAt_keep_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {a : Adr} {code : ByteArray}
    (block : ConfiguredBlockTraceIn F cfg pre post) (fork : block.fork = .cancun)
    (avoid : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (installed : pre.state.getCode a = code)
    (nonempty : code.toList ≠ []) (ordinary : ¬ isValidDelegation code) :
    post.state.getCode a = code := by
  have rules : (initBenv block.fork pre block.block.header).stat.rules = Fork.ruleSet .cancun := by
    change Fork.ruleSet block.fork = _
    rw [fork]
  have final := block.bodyTrace.codeAt_keep_noStateGas
    (by rw [rules]; rfl) (by rw [rules]; rfl)
    (by change (initBenv block.fork pre block.block.header).stat.rules.settle.refundQuotient = 5
        rw [rules]; rfl)
    (by change (initBenv block.fork pre block.block.header).stat.rules.settle.touchedSweep = false
        rw [rules]; rfl)
    (Or.inl (by rw [rules]; rfl)) avoid installed nonempty ordinary AdrSet.not_mem_empty
  rw [block.postEq]
  exact final

/-- One beacon-code checkpoint and CREATE avoidance derive every later
opening's installation condition and the actual final beacon code. -/
theorem MidHistoryTraceIn.beaconCodeInstalled_of_checkpoint_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) (forks : trace.AllCancun)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress)
    (installed : start.state.getCode beaconRootsAddress = beaconRootsCode) :
    trace.BeaconCodeInstalled ∧ future.state.getCode beaconRootsAddress = beaconRootsCode := by
  have facts := systemContracts_facts _ (List.mem_cons_self)
  induction trace with
  | tail block cut =>
    exact ⟨trivial, block.tail_codeAt_keep_cancun cut forks avoid installed facts.2.2 facts.2.1⟩
  | step prior block ih =>
    obtain ⟨priorInstalled, middleCode⟩ := ih forks.1
      (fun root member => avoid root (List.mem_append_left _ member)) installed
    exact ⟨⟨priorInstalled, middleCode⟩,
      block.codeAt_keep_cancun forks.2
        (fun root member => avoid root (List.mem_append_right _ member))
        middleCode facts.2.2 facts.2.1⟩

/-- A single actual beacon checkpoint can supply the caller producer's residual
installation premise, with explicit CREATE avoidance at the beacon account. -/
theorem MidHistoryTraceIn.frameAdmitted_caller_ne_of_beacon_checkpoint_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {a ca : Adr}
    (trace : MidHistoryTraceIn F cfg start future) (forks : trace.AllCancun)
    (senders : trace.NoSenderAt a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty)
    (beaconAvoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress)
    (beacon : start.state.getCode beaconRootsAddress = beaconRootsCode)
    (target : ca ≠ beaconRootsAddress) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.caller ≠ a) :=
  trace.frameAdmitted_caller_ne_cancun forks senders
    (trace.beaconCodeInstalled_of_checkpoint_cancun forks beaconAvoid beacon).1 avoid empty target

end Blanc.ExecutionTrace
