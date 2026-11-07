import Blanc.Lift.ApprovalLog
import Blanc.Lift.Usdc.V2_1Frames
import Blanc.Lift.Usdc.V2_1TransferWithAuthorizationReach

/-!
# USDC FiatTokenV2_1: `permit` logs `Approval`

`permit` is V2_1's one setter a signature names. It reaches entry 79, `_approve`, which stores and logs. Signature recovery
is not walked: the frame commits whatever it returns, and a committed frame logs.
-/

namespace Blanc.Lift.CurveCoins.UsdcV2_1

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.ImplV2_1

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **Entry 79, `_approve(owner, spender, value)`.** -/
theorem e79_log {v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: w :: ret :: S) M G) t_39da_c79 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  clear h
  simp only [word_ff20, ff20_and_word, toAdr_toB256] at e
  rw [approvalTopic_bytes] at e
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- The internal callees of `permit`: none halts the frame. -/
def permitCallees : List Nat := [7, 24, 71, 79, 83, 89]

theorem permitCallees_noHalt : NoHaltSet cert.prog permitCallees = true := by decide +kernel

/-- **Entry 71, `_permit`.** -/
theorem e71_log {sigS sigR sigV dl v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: dl :: v :: a :: w :: ret :: S) M G) t_410c_c71 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  iterate 1 ustep h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨_, e⟩ := ri_timestamp hd
  subst e
  clear hd
  repeat ustep h
  ibranch h c1
  repeat ustep h
  have h' := ric_callR (k := 83) (g := t_46b5_c83) rfl
    (fun hh => SFunc.RunP.not_halted_entry permitCallees_noHalt (by decide : 83 ∈ permitCallees) rfl hh rfl) h
  clear h
  obtain ⟨_, D, hc, h⟩ := h'
  obtain ⟨res, stack⟩ := Usdc.V2_1TransferWithAuthorizationReach.signature_return_stack (fun x => x) fork.stateGas_none hc
  rw [St.self' D, stack] at h
  clear hc
  repeat ustep h
  ibranch h c2
  repeat ustep h
  have h' := ric_callR (k := 79) (g := t_39da_c79) rfl
    (fun hh => SFunc.RunP.not_halted_entry permitCallees_noHalt (by decide : 79 ∈ permitCallees) rfl hh rfl) h
  clear h
  obtain ⟨_, _, hc, h⟩ := h'
  obtain ⟨b₀, data, M', G', e⟩ := e79_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 24, `permit`'s guards.** -/
theorem e24_log {sigS sigR sigV dl v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: dl :: v :: a :: w :: ret :: S) M G) t_3092_c24 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 71) (g := t_410c_c71) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e71_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e71_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **A committed `permit` logs `Approval` with its named owner.** -/
theorem frame_permit_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xd505accf)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, (Sevm.dataWord sevm 4).toAdr.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 24) (g := t_3092_c24) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e24_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e24_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

end Blanc.Lift.CurveCoins.UsdcV2_1
