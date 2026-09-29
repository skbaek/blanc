import Blanc.Lift.Weth9.CommittedSpawn
import Blanc.ExecutionAccountingAdmission

/-!
# WETH9 history identified with its committed writer invocations

The third consumer of the generic accounting ladder (`Exec.coreAccounting`,
`AccountingLadderAdmitted.configuredHistory`), after the beacon deposit contract and Curve, and the first
whose target frame spawns a child *after* its own effect: `withdraw` debits and then sends ETH to the
caller, who may re-enter the contract from inside the send.  The replay boundary is the ledger the contract's
storage carries over the trace-fixed universe of tracked keys (`wethCarrier`); the observation is the ordered
list of committed writer invocations at the contract (`committedInvocations`); the target frame's own step
comes before the steps of the children it settles (`Blanc/ExecutionModelAccounting.lean`).

`weth9_history_committed` is the headline: from one initial footprint and the trace-local freshness of the
keys the trace touches, the future footprint ledger is the model run (`Ledger.run`) over exactly the
settlement-committed WETH9 writer invocations at the contract, in trace order.  Rolled-back frames are not in
the list, views contribute nothing, and calls re-entered from inside `withdraw`'s ETH send appear in their
place: after the `withdraw` that opened them.  The model, run with the contract's ETH alongside
(`State.run`), stays backed.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The observation of a static frame is empty. -/
theorem committedFrameInvocations_static {ca : Adr} {f : Exec.Frame} (h : f.sevm.isStatic = true) :
    committedFrameInvocations ca f = [] := by
  unfold committedFrameInvocations
  simp [h]

/-- The observation of a frame at another address is empty. -/
theorem committedFrameInvocations_foreign {ca : Adr} {f : Exec.Frame}
    (h : f.sevm.currentTarget ≠ ca) : committedFrameInvocations ca f = [] := by
  unfold committedFrameInvocations
  simp [h]

/-- **The accounting ladder of the WETH9 ledger replay** over a tracked universe `U` with injective slots:
the footprint frame theorem, the spawn obligations of `withdraw`, and the generic ladder for everything
else. -/
noncomputable def weth9AccountingLadder (ca : Adr) {U : Key → Prop} (hinj : KeyInj U) :
    AccountingLadderAdmitted (footSpec U) ca (footEntry U) :=
  modelLadder (c := footSpec U) (wethCarrier ca U) (wethObservation ca U) LedgerReplay.append
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun {_ _} h => ledger_congr_get h)
    (fun f hf => committedFrameInvocations_static hf)
    (fun f hf => committedFrameInvocations_foreign hf)
    (weth9_spawnKinds ca) (weth9_spawnReplay ca hinj) (footSpec_preservesAdmitted ca hinj)

/-- **The WETH9 model replays the committed chain.**  In a configured history from a checkpoint with the
footprint `K₀` (one initial footprint; the code installed), whose touched keys are fresh against it (the
trace-local hash premise), the deployed WETH9's footprint ledger at the future state is the model
run (`Ledger.run`) of exactly the writer invocations of the settlement-committed frames at the contract, in
trace order (`committedInvocations`), from the footprint ledger at the checkpoint.  The list is definitional,
not chosen: each invocation is a settled non-static frame at the contract whose calldata decodes as a writer
(`decodeCall`), rolled-back frames are never in it, views contribute nothing, and a call re-entered from
inside `withdraw`'s ETH send comes after the `withdraw` that sent it.  Alongside: the deployed code is intact,
the ether does not overflow, the future storage carries the footprint `K₀ ∪ touched`
(`weth9_history_footprint_universe`), and the model run with the contract's ETH is backed (`State.run`,
`State.run_backed`): the booked total never exceeds the ether the run's calls moved in and out. -/
theorem weth9_history_committed {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (historyKeyUniverse ca trace K₀) (future.state.getStor ca) (future.state.bal ca) ∧
      (ledger K₀ (checkpoint.state.getStor ca)).run
          (replayCalls (committedInvocations ca trace)) =
        some (ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca)) ∧
      ∃ s : State,
        (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat).run
            (replayCalls (committedInvocations ca trace)) = some s ∧
          s.ledger = ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca) ∧
          s.Backed := by
  let U := historyKeyUniverse ca trace K₀
  have extended : FootInv U (checkpoint.state.getStor ca) (checkpoint.state.bal ca) :=
    initial.extend fresh
  have admitted : trace.FrameAdmitted ca (footEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have start : (footSpec U).StateInv ca checkpoint.state :=
    footSpec_stateInv_iff.mpr ⟨installed, sumNof, extended.support, extended.backed⟩
  have finish := trace.stateInv_admitted_sem (footSpec_preservesAdmitted ca extended.inj)
    admitted start
  obtain ⟨hcode, hside, hsup, hback⟩ := footSpec_stateInv_iff.mp finish
  obtain ⟨steps, replay, observed⟩ :=
    (weth9AccountingLadder ca extended.inj).configuredHistory trace admitted start
  change LedgerReplay (ledger U (checkpoint.state.getStor ca)) steps
    (ledger U (future.state.getStor ca)) at replay
  change steps = trace.settledFrames.flatMap (committedFrameInvocations ca) at observed
  have hsteps : steps = committedInvocations ca trace := observed
  subst hsteps
  have hrun : (ledger K₀ (checkpoint.state.getStor ca)).run
      (replayCalls (committedInvocations ca trace)) = some (ledger U (future.state.getStor ca)) := by
    have := replay
    unfold LedgerReplay at this
    have hext : ledger U (checkpoint.state.getStor ca) = ledger K₀ (checkpoint.state.getStor ca) :=
      ledger_extend initial fresh
    rw [hext] at this
    exact this
  refine ⟨hcode, hside, ⟨hsup, extended.inj, extended.apart, hback⟩, hrun, ?_⟩
  have hmodel := State.run_ledger
    (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat)
    (replayCalls (committedInvocations ca trace))
  simp only [hrun] at hmodel
  cases hs : (State.mk (ledger K₀ (checkpoint.state.getStor ca))
      (checkpoint.state.bal ca).toNat).run (replayCalls (committedInvocations ca trace)) with
  | none => rw [hs] at hmodel; cases hmodel
  | some s =>
    rw [hs] at hmodel
    simp only [Option.map_some, Option.some.injEq] at hmodel
    refine ⟨s, rfl, hmodel, ?_⟩
    exact State.run_backed (s := ⟨ledger K₀ (checkpoint.state.getStor ca),
      (checkpoint.state.bal ca).toNat⟩) initial.backed hs

end Blanc.Lift.Weth9
