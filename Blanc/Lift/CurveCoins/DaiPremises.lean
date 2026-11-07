import Blanc.Lift.LogFilterPremises
import Blanc.Lift.CurveCoins.ApprovalLogsDai

/-!
# DAI's premises, from logs

* `dai_noSignature_of_receipts`: no `Approval` naming the holder as owner gives DAI's `noSignature`;
* `dai_rows_of_logs`: over a history from a state with the holder's tracked rows empty, no `Approval` naming it keeps them
  empty.

Receipts do not speak for system stages, so the receipt form takes `sysNe`. `MidHistoryTraceIn.system_ne` gives it from
`SystemConfined` for a coin outside the four system addresses.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}

namespace Dai

open Blanc.Lift.Dai Blanc.Lift.CurveCoins.Dai

/-- **DAI's `noSignature` from no `Approval(h, _)` receipt log.** -/
theorem dai_noSignature_of_receipts (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code) (receipts : trace.NoLogInReceipts (ApprovalLog T h))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ SignedAs h F.sevm :=
  dai_noSignature_of_logs trace installed fun F hF ⟨l, mem, addr, topics⟩ =>
    trace.no_log_at HistFork.stateGas_none _ receipts sysNe F (mem_coinFrames.mp hF).1 (mem_coinFrames.mp hF).2.1 l mem
      ⟨addr, topics⟩

/-- **The holder's tracked rows, across a history from a state with them empty**, when no frame logs `Approval` naming
it. `frames` as in `Usdt.usdt_rows_of_logs`. -/
theorem dai_rows_of_logs (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code)
    {frames : List Exec.Frame} (sub : coinFrames T (fun _ => True) trace.settledFrames ⊆ frames)
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) (rows : RowsEmpty h frames (wordsAt T start.state))
    (noLog : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ∀ l ∈ F.post.logs, ¬ ApprovalLog T h l) :
    RowsEmpty h frames (wordsAt T future.state) := by
  refine ((dai_chain trace installed).1 (fun _ _ => trivial) |>.fold (held := fun _ => 0) (credit := fun _ => 0)
    (debit := fun _ => 0) (I := RowsEmpty h frames) (fun F hF good empty => ⟨?_, Nat.le_refl _⟩) rows).1
  refine Classical.byContradiction fun raised => ?_
  have target := (mem_coinFrames.mp hF).2.1
  obtain ⟨l, mem, addr, topics⟩ := frame_rows_raised_logs (sub hF) good target
    (CertFrame.of_staticOnly cert_check staticOnly HistFork.stateGas_none good target) keys empty raised
  exact noLog F hF l mem ⟨addr, topics⟩

end Dai

end Blanc.Lift.CurveCoins
