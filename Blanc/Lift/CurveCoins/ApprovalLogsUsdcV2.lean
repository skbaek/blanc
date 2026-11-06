import Blanc.Lift.CurveCoins.ApprovalLog
import Blanc.Lift.Usdc.V2Frames
import Blanc.Lift.Usdc.V2TransferWithAuthorizationReach
import Blanc.Lift.Usdc.AllowLocality

/-!
# USDC FiatTokenV2: every allowance setter logs `Approval`

`implV2_allowSitesOk` certifies `selV2`: three caller-keyed writers (`approve`, `increaseAllowance`, `decreaseAllowance`),
four owner-keyed (`permit` and the three `...WithAuthorization`), and two initializers. All seven setters reach entry 81,
`_approve`, which stores and logs. `allowedFrame_logs` collects them. Signature recovery is not walked: the frames commit
whatever it returns, and a committed frame logs.
-/

namespace Blanc.Lift.CurveCoins.UsdcV2

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.ImplV2

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- The internal callees of the allowance setters: none halts the frame. -/
def setterCallees : List Nat := [5, 6, 75, 77, 78, 79, 81, 83, 84, 85, 88, 89, 91, 93]

theorem setterCallees_noHalt : NoHaltSet cert.prog setterCallees = true := by decide +kernel

/-- Enter callee entry `k` (tree `T`) of `setterCallees` from a cut run `h`. -/
macro "scall " h:ident hc:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry setterCallees_noHalt
      (by decide : $k ∈ setterCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, _, $hc:ident, $h:ident⟩ := h'))

/-- `ric_call` with both arms, for an entry whose law says it returns. -/
macro "scall' " h:ident hc:ident k:num T:term : tactic => `(tactic|
  obtain ⟨_, ⟨_, $hc:ident, $h:ident⟩ | ⟨_, $hc:ident, -⟩⟩ := ric_call (k := $k) (g := $T) rfl $h)

/-- `scall`, naming the returned state. -/
macro "scallD " h:ident hc:ident D:ident k:num T:term : tactic => `(tactic|
  (have h' := ric_callR (k := $k) (g := $T) rfl
    (fun hh => SFunc.RunP.not_halted_entry setterCallees_noHalt
      (by decide : $k ∈ setterCallees) rfl hh rfl) $h
   clear $h
   obtain ⟨_, $D:ident, $hc:ident, $h:ident⟩ := h'))

/-- **Entry 81, `_approve(owner, spender, value)`**: the shared setter. -/
theorem e81_log {v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: w :: ret :: S) M G) t_3db1_c81 o) :
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

/-- **Entry 61, `approve`'s guards.** -/
theorem e61_log {v a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: ret :: S) M G) t_0f56_c61 o) :
    ∃ (b₀ : Devm) (data : Bytes) (r : B256) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, a.toAdr.toB256], data⟩) (r :: S) M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 81) (g := t_3db1_c81) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e81_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e81_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  simp only [toAdr_toB256] at e
  exact ⟨_, _, _, _, _, Seg.done.inj e⟩

/-- **A committed `approve` logs `Approval` with its caller.** -/
theorem frame_approve_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧ l.topics.take 2 = [approvalTopic, sevm.caller.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 61) (g := t_0f56_c61) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, _, e⟩ := e61_log fork hc; cases e
  obtain ⟨b₀, data, r, M', G', e⟩ := e61_log fork hc
  cases e
  clear hc
  repeat ustep h
  rw [ric_return_logs h]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **Entry 79, `_increaseAllowance`.** -/
theorem e79_log {v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: w :: ret :: S) M G) t_41b3_c79 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  scall h hc 77 t_41fd_c77
  obtain ⟨-, G1, e⟩ := e77_inv fork hc
  cases e
  clear hc
  repeat ustep h
  scall h hc 81 t_3db1_c81
  obtain ⟨b₀, data, M', G', e⟩ := e81_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 75, `_decreaseAllowance`.** -/
theorem e75_log {v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: w :: ret :: S) M G) t_43fa_c75 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  iterate 22 ustep h
  have h' := ric_next h
  clear h
  obtain ⟨_, hd, h⟩ := h'
  obtain ⟨_, e⟩ := ri_codecopy hd
  subst e
  clear hd
  repeat ustep h
  scall h hc 88 t_4be2_c88
  obtain ⟨-, G1, e⟩ := e88_inv fork hc
  cases e
  clear hc
  repeat ustep h
  scall h hc 81 t_3db1_c81
  obtain ⟨b₀, data, M', G', e⟩ := e81_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 85, the authorization's use**: it leaves the stack below its arguments. -/
theorem e85_ret {n w tag : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (n :: w :: tag :: S) M G) t_4e5e_c85 o) :
    ∃ (b' : Devm) (M' : Mem) (G' : Nat), o = .returned (St b' S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, Seg.done.inj e⟩

/-- **Entry 66, the signed allowance body.** -/
theorem e66_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_4976_c66 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  scallD h hc D 83 t_4d9e_c83
  rw [St.self' D, Usdc.V2TransferWithAuthorizationReach.validity_return_stack (fun x => x) fork.stateGas_none hc] at h
  clear hc
  repeat ustep h
  scallD h hc D 84 t_4d2c_c84
  obtain ⟨res, stack⟩ := Usdc.V2TransferWithAuthorizationReach.signature_return_stack (fun x => x) fork.stateGas_none hc
  rw [St.self' D, stack] at h
  clear hc
  repeat ustep h
  ibranch h c1
  repeat ustep h
  scall h hc 85 t_4e5e_c85
  obtain ⟨b1, M1, G1, e⟩ := e85_ret fork hc
  cases e
  clear hc
  repeat ustep h
  scall h hc 81 t_3db1_c81
  obtain ⟨b₀, data, M', G', e⟩ := e81_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 70, the signed allowance body.** -/
theorem e70_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_4625_c70 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  scallD h hc D 83 t_4d9e_c83
  rw [St.self' D, Usdc.V2TransferWithAuthorizationReach.validity_return_stack (fun x => x) fork.stateGas_none hc] at h
  clear hc
  repeat ustep h
  scallD h hc D 84 t_4d2c_c84
  obtain ⟨res, stack⟩ := Usdc.V2TransferWithAuthorizationReach.signature_return_stack (fun x => x) fork.stateGas_none hc
  rw [St.self' D, stack] at h
  clear hc
  repeat ustep h
  ibranch h c1
  repeat ustep h
  scall h hc 85 t_4e5e_c85
  obtain ⟨b1, M1, G1, e⟩ := e85_ret fork hc
  cases e
  clear hc
  repeat ustep h
  scall h hc 79 t_41b3_c79
  obtain ⟨b₀, data, M', G', e⟩ := e79_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 72, the signed allowance body.** -/
theorem e72_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_4456_c72 o) :
    ∃ (b₀ : Devm) (data : Bytes) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, w.toAdr.toB256, a.toAdr.toB256], data⟩) S M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  scallD h hc D 83 t_4d9e_c83
  rw [St.self' D, Usdc.V2TransferWithAuthorizationReach.validity_return_stack (fun x => x) fork.stateGas_none hc] at h
  clear hc
  repeat ustep h
  scallD h hc D 84 t_4d2c_c84
  obtain ⟨res, stack⟩ := Usdc.V2TransferWithAuthorizationReach.signature_return_stack (fun x => x) fork.stateGas_none hc
  rw [St.self' D, stack] at h
  clear hc
  repeat ustep h
  ibranch h c1
  repeat ustep h
  scall h hc 85 t_4e5e_c85
  obtain ⟨b1, M1, G1, e⟩ := e85_ret fork hc
  cases e
  clear hc
  repeat ustep h
  scall h hc 75 t_43fa_c75
  obtain ⟨b₀, data, M', G', e⟩ := e75_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 48, `increaseAllowance`'s guards.** -/
theorem e48_log {v a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: ret :: S) M G) t_1afe_c48 o) :
    ∃ (b₀ : Devm) (data : Bytes) (r : B256) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, a.toAdr.toB256], data⟩) (r :: S) M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  scall h hc 79 t_41b3_c79
  obtain ⟨b₀, data, M', G', e⟩ := e79_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  simp only [toAdr_toB256] at e
  exact ⟨_, _, _, _, _, Seg.done.inj e⟩

/-- **Entry 33, `decreaseAllowance`'s guards.** -/
theorem e33_log {v a ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (v :: a :: ret :: S) M G) t_2a36_c33 o) :
    ∃ (b₀ : Devm) (data : Bytes) (r : B256) (M' : Mem) (G' : Nat), o = .returned (St
      (Devm.addLog b₀ ⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, a.toAdr.toB256], data⟩) (r :: S) M' G') := by
  have h := run.cut
  clear run
  repeat ustep h
  ibranch h c1
  repeat ustep h
  ibranch h c2
  repeat ustep h
  ibranch h c3
  repeat ustep h
  scall h hc 75 t_43fa_c75
  obtain ⟨b₀, data, M', G', e⟩ := e75_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  simp only [toAdr_toB256] at e
  exact ⟨_, _, _, _, _, Seg.done.inj e⟩

/-- **A committed `increaseAllowance` logs `Approval` with its caller.** -/
theorem frame_increaseAllowance_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0x39509351)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧ l.topics.take 2 = [approvalTopic, sevm.caller.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 48) (g := t_1afe_c48) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, _, e⟩ := e48_log fork hc; cases e
  obtain ⟨b₀, data, r, M', G', e⟩ := e48_log fork hc
  cases e
  clear hc
  repeat ustep h
  rw [ric_return_logs h]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **A committed `decreaseAllowance` logs `Approval` with its caller.** -/
theorem frame_decreaseAllowance_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xa457c2d7)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧ l.topics.take 2 = [approvalTopic, sevm.caller.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 33) (g := t_2a36_c33) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, _, e⟩ := e33_log fork hc; cases e
  obtain ⟨b₀, data, r, M', G', e⟩ := e33_log fork hc
  cases e
  clear hc
  repeat ustep h
  rw [ric_return_logs h]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **Entry 14, `approveWithAuthorization`'s guards.** -/
theorem e14_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_3761_c14 o) :
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
  scall' h hc 66 t_4976_c66
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e66_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e66_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 21, `increaseAllowanceWithAuthorization`'s guards.** -/
theorem e21_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_328f_c21 o) :
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
  scall' h hc 70 t_4625_c70
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e70_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e70_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 25, `decreaseAllowanceWithAuthorization`'s guards.** -/
theorem e25_log {sigS sigR sigV n x y v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: n :: x :: y :: v :: a :: w :: ret :: S) M G) t_3033_c25 o) :
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
  scall' h hc 72 t_4456_c72
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e72_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e72_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **A committed `approveWithAuthorization` logs `Approval` with its named owner.** -/
theorem frame_approveWithAuthorization_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xe1560fd3)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, (Sevm.dataWord sevm 4).toAdr.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 14) (g := t_3761_c14) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e14_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e14_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **A committed `increaseAllowanceWithAuthorization` logs `Approval` with its named owner.** -/
theorem frame_increaseAllowanceWithAuthorization_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xc237108f)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, (Sevm.dataWord sevm 4).toAdr.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 21) (g := t_328f_c21) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e21_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e21_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **A committed `decreaseAllowanceWithAuthorization` logs `Approval` with its named owner.** -/
theorem frame_decreaseAllowanceWithAuthorization_logs {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (sel : Blanc.Sevm.selector sevm = 0xb0086095)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧
      l.topics.take 2 = [approvalTopic, (Sevm.dataWord sevm 4).toAdr.toB256] := by
  have h := run.cut
  clear run
  uhead h sel
  repeat ustep h
  ibranch h c1
  repeat ustep h
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 25) (g := t_3033_c25) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e25_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e25_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-- **Entry 71, `_permit`.** -/
theorem e71_log {sigS sigR sigV dl v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: dl :: v :: a :: w :: ret :: S) M G) t_475b_c71 o) :
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
  scallD h hc D 84 t_4d2c_c84
  obtain ⟨res, stack⟩ := Usdc.V2TransferWithAuthorizationReach.signature_return_stack (fun x => x) fork.stateGas_none hc
  rw [St.self' D, stack] at h
  clear hc
  repeat ustep h
  ibranch h c2
  repeat ustep h
  scall h hc 81 t_3db1_c81
  obtain ⟨b₀, data, M', G', e⟩ := e81_log fork hc
  cases e
  clear hc
  repeat ustep h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, _, _, Seg.done.inj e⟩

/-- **Entry 23, `permit`'s guards.** -/
theorem e23_log {sigS sigR sigV dl v a w ret : B256} {o : Outcome} (fork : HistFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (sigS :: sigR :: sigV :: dl :: v :: a :: w :: ret :: S) M G) t_3450_c23 o) :
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
  scall' h hc 71 t_475b_c71
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
  obtain ⟨_, ⟨_, hc, h⟩ | ⟨_, hc, -⟩⟩ := ric_call (k := 23) (g := t_3450_c23) rfl h
  on_goal 2 => obtain ⟨_, _, _, _, e⟩ := e23_log fork hc; cases e
  obtain ⟨b₀, data, M', G', e⟩ := e23_log fork hc
  cases e
  clear hc
  repeat ustep h
  cases ric_stop h
  simp only [ff20_and_word, word_ff20, toAdr_toB256, lit4]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl⟩

/-! ## What a frame of this code does to a row -/

open Blanc.Lift.WriteSite in
/-- **A committed V2 frame whose selector is on the row table logs `Approval` with the row's owner.** `selV2`'s
callers log with the caller, its owners with the named word; `implV2_allowSitesOk` certifies the table. So a store that
raises a tracked row in a committed frame, other than through an initializer, logs. -/
theorem allowedFrame_logs {pair : Adr} {post : Devm} (fork : HistFork sevm.benvStat.fork)
    (allowed : AllowedFrame Usdc.selV2 pair (Env.root sevm))
    (notInit : Blanc.Sevm.selector sevm ≠ 0x3357162b ∧ Blanc.Sevm.selector sevm ≠ 0xd608ea64)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    ∃ l ∈ post.logs, l.address = sevm.currentTarget ∧ l.topics.take 2 = [approvalTopic, pair.toB256] := by
  have root : Usdc.selV2T.eval (Env.root sevm) = Blanc.Sevm.selector sevm := by
    have shift : (0xe0 : B256).toNat = 224 := by decide
    change Sevm.dataWord sevm 0 >>> (0xe0 : B256).toNat = Sevm.dataWord sevm 0 >>> 224
    rw [shift]
  rcases allowed with ⟨sel, caller⟩ | ⟨sel, named⟩ | sel
  · have hc : sevm.caller = pair := by
      have e : (Env.root sevm).caller = sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256] at caller
      exact caller
    subst hc
    change Usdc.selV2T.eval (Env.root sevm) ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] at sel
    rw [root] at sel
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sel
    rcases sel with s | s | s
    · exact frame_approve_logs fork s run
    · exact frame_increaseAllowance_logs fork s run
    · exact frame_decreaseAllowance_logs fork s run
  · have hn : (Sevm.dataWord sevm 4).toAdr = pair := named
    subst hn
    change Usdc.selV2T.eval (Env.root sevm) ∈ [0xd505accf, 0xe1560fd3, 0xc237108f, 0xb0086095] at sel
    rw [root] at sel
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sel
    rcases sel with s | s | s | s
    · exact frame_permit_logs fork s run
    · exact frame_approveWithAuthorization_logs fork s run
    · exact frame_increaseAllowanceWithAuthorization_logs fork s run
    · exact frame_decreaseAllowanceWithAuthorization_logs fork s run
  · change Usdc.selV2T.eval (Env.root sevm) ∈ Usdc.selV2.inits at sel
    rw [root] at sel
    simp only [Usdc.selV2, List.mem_cons, List.not_mem_nil, or_false] at sel
    rcases sel with s | s
    · exact absurd s notInit.1
    · exact absurd s notInit.2

/-- **A committed V2 frame with a store that raises one of `pair`'s tracked rows, other than an initializer, logs
`Approval` with `pair` as owner.** `sep` is hash freshness for the frame, as in `implV2_allowLocality`. -/
theorem row_raised_logs {pair : Adr} {Tr : Adr → Prop} {F : Exec.Frame} (hpc : F.pc = 0) (hcode : F.sevm.code = code)
    (fork : HistFork F.sevm.benvStat.fork) {node : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv F) node) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? node = some w)
    (sep : WriteSite.RowSep 10 pair.toB256 (WriteSite.AllowKey Tr) (WriteSite.wsRoot Usdc.ImplV2Ws.implWsAnn)
      (WriteSite.Env.root F.sevm))
    (tracked : ∃ g, Tr g ∧ Usdc.allowSlot pair g = w.key)
    (raises : (node.devm.getStorVal node.sevm.currentTarget w.key).toNat < w.value.toNat)
    (notInit : Blanc.Sevm.selector F.sevm ≠ 0x3357162b ∧ Blanc.Sevm.selector F.sevm ≠ 0xd608ea64) :
    FrameLogsApproval F.sevm.currentTarget pair F := by
  rcases WriteSite.rawWrite_rowClass (G := Exec.Frame.rootDeriv F) (t := Usdc.selV2) (b := 10) hpc fork.stateGas_none chain cert_check
    Usdc.implV2_wsCert hcode (by decide) Usdc.implV2_allowSitesOk sep found tracked with allowed | le
  · obtain ⟨pc, sevm, pre, out, run, committed⟩ := F
    dsimp only [Exec.Frame.rootDeriv] at hpc chain hcode fork allowed notInit ⊢
    subst hpc
    cases out with
    | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
      obtain ⟨f, hf0, hrun⟩ := lift_sound_noStateGas cert_check hcode fork.stateGas_none run
      obtain rfl : f = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
      rw [St.self' pre] at hrun
      exact allowedFrame_logs fork allowed notInit hrun
  · exact absurd raises (Nat.not_lt.mpr le)

end Blanc.Lift.CurveCoins.UsdcV2
