import Blanc.Lift.Curve3Crv.HistCommittedHistory
import Blanc.ExecutionMidWindowIn

/-!
# 3Crv's committed history over a window between two cuts

`c3crv_mid_history_framesHist` over a window that stops right after a transaction of its last block
(`AccountingLadderAdmittedIn.midWindowIn`). The collision universe is still that of the mid history
running on to the end of the block, so one `FreshKeys` premise serves both.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The settlement-committed writer invocations at the contract of a window, in trace order. -/
def windowCommittedInvocationsIn {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (ca : Adr) (mid : MidHistoryTraceIn HistFork cfg start pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) : List WriterInvocation :=
  (mid.settledFrames ++ block.settledThroughCut cut).flatMap (committedFrameInvocations ca)

/-- **The committed chain of a window, frame by frame.** The statement of
`c3crv_mid_history_framesHist` at the state right after transaction `i` of the window's last block. -/
theorem c3crv_window_framesHist {ca : Adr} {cfg : ChainConfig} {start : Benv}
    {pre post : BlockChain} {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (mid : MidHistoryTraceIn HistFork cfg start pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (installed : some (start.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (start.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (midTouchedKeysIn ca (mid.step block))) :
    some (cut.afterBenv.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRunBy OwnerAnswerH initial (windowCommittedInvocationsIn ca mid block cut) s ∧
        VyInv (cut.afterBenv.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (windowCommittedInvocationsIn ca mid block cut))) := by
  let trace := mid.step block
  let U := Key.extend initialKeys (midTouchedKeysIn ca trace)
  have topology : VyInv (start.state.getStor ca) initial U := invariant.extend fresh
  have capabilities := BodyStageCapabilities.historical
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target
    refine ⟨trace.rawFrames_entered enteredCondition_fresh root member,
      trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge) root member,
      fun k hk => Or.inr ?_⟩
    exact List.mem_flatMap.mpr ⟨root, member, by simpa only [target, ite_true] using hk⟩
  have startInv : (curveSpec U).StateInv ca start.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨⟨steps, replay, observed⟩, finish, -⟩ :=
    (curveAccountingLadderIn HistFork HistFork.stateGas_none ca U topology.inj
      topology.apart).midWindowIn mid block cut admitted.1 admitted.2 capabilities
      (mid.rewardCreditsFunded capabilities) startInv c3crvInstalledCert.runtimeSafety rfl
  change CurveFrameReplayBy OwnerAnswerH ca U (start.state.getStor ca) steps
    (cut.afterBenv.state.getStor ca) at replay
  change steps = windowCommittedInvocationsIn ca mid block cut at observed
  subst observed
  obtain ⟨s, run, -, final⟩ := replay.2 initial initialKeys (fun _ hk => Or.inl hk) invariant
  exact ⟨finish.code, s, run, final⟩

end Blanc.Lift.Curve3Crv
