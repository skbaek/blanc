import Blanc.Lift.CurveCoins.ApprovalLog
import Blanc.Lift.CurveCoins.DaiLocality

/-!
# DAI: a frame that raises an allowance row from zero logs `Approval` with that owner

`frame_approve_logs` walks `approve`; `frame_permit_logs` (`DaiPermit.lean`) walked `permit`. `rowTable_ok` certifies
that those two selectors are DAI's only row writers, so `frame_rows_raised_logs` follows: a committed frame that
raises one of the holder's tracked rows from empty logs `Approval` with the holder as owner.
-/

namespace Blanc.Lift.CurveCoins.Dai

open Jaune Blanc Blanc.Lift Blanc.Lift.Dai Blanc.Lift.WriteSite Blanc.ExecutionTrace

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The entries `approve` calls: none halts the frame. -/
def approveCallees : List Nat := [32]

theorem approveCallees_noHalt : NoHaltSet cert.prog approveCallees = true := by decide +kernel

/-- **Entry 32, `approve`'s body.** -/
theorem e32_log {v sp ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: sp :: ret :: S) M G) t_092d_c32 o) :
    ∃ (b₀ : Devm) (data : Bytes) (r : B256) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, sp.toAdr.toB256], data⟩)
        (r :: S) M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  simp only [ff20_and_word, toAdr_toB256] at e
  rw [approvalTopic_bytes] at e
  exact ⟨_, _, _, _, _, Seg.done.inj e⟩

/-- **A committed `approve` logs `Approval` with its caller.** -/
theorem frame_approve_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, sevm.caller.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  have h' := ric_callR (k := 32) (g := t_092d_c32) rfl
    (fun hh => SFunc.RunP.not_halted_entry approveCallees_noHalt
      (by decide : 32 ∈ approveCallees) rfl hh rfl) h
  clear h
  obtain ⟨_, _, hc, h⟩ := h'
  obtain ⟨b₀, data, r, M', G', e⟩ := e32_log fork hc
  cases e
  clear hc
  repeat ustep h
  rw [ric_return_logs h]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, by
    simp only [List.take_succ_cons, List.take_zero]⟩

/-- A committed `approve` by the holder logs `Approval` with the holder, at `T`. -/
theorem approve_logs {T h : Adr} {F : Exec.Frame} (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3)
    (hc : F.sevm.caller = h) : LogsApprovalAs T h F := by
  obtain ⟨S, M, G, run⟩ := codeFrame_run good
  obtain ⟨l, mem, addr, topics⟩ := frame_approve_logs good.2.2.1 hsel run
  exact ⟨l, mem, addr.trans target, by rw [topics, hc]; rfl⟩

/-- **A committed frame that raises one of the holder's tracked rows from empty logs `Approval` with the
holder as owner.** `rowTable_ok` certifies `approve` and `permit` as DAI's only row writers. -/
theorem frame_rows_raised_logs {T h : Adr} {frames : List Exec.Frame} {F : Exec.Frame} (hF : F ∈ frames)
    (good : CodeFrame T HistFork code F) (target : F.sevm.currentTarget = T) (C : CertFrame F code T)
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames)
    (rows : RowsEmpty h frames (wordsAt T F.pre.state))
    (raised : ¬ RowsEmpty h frames (wordsAt T F.post.state)) : LogsApprovalAs T h F := by
  refine Classical.byContradiction fun noLog => raised ?_
  refine frame_rows_zero C cert_check dai_wsCert (t := rowTable) (b := 3) rfl rowTable_ok
    (rowSep_of_keys keys hF) ?_ rows
  rintro (⟨sel, caller⟩ | ⟨sel, named⟩ | sel)
  · have hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3 := by
      have := List.mem_singleton.mp sel
      rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
    have hc : F.sevm.caller = h := by
      have e : (Env.root F.sevm).caller = F.sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256] at caller
      exact caller
    exact noLog (approve_logs good target hsel hc)
  · have hsel : Blanc.Sevm.selector F.sevm = 0x8fcbaf0c := by
      have := List.mem_singleton.mp sel
      rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
    exact noLog (signedAs_logs good target ⟨hsel, named⟩)
  · exact absurd sel List.not_mem_nil

end Blanc.Lift.CurveCoins.Dai
