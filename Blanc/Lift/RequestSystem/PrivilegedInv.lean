import Blanc.Lift.RequestSystem.PathInv

/-! A successful request-system prefix, independent of the store gas backend.
The callback observes actual successful stores; it requires no ready reservoir,
chosen gas, fresh storage, or empty memory. -/

namespace Blanc.Lift.RequestSystem

open Jaune
open RequestFee (PushWord)

/-- Only the observable effects needed by the inverse, read from an actual store. -/
def StoreInv (sevm : Sevm) : Prop :=
  ∀ {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {key value : B256},
    Ninst.Run sevm (St b (key :: value :: S) M G) (.reg .sstore) d →
    sevm.isStatic = false ∧ ∃ b' G', d = St b' S M G' ∧
      b'.state = b.state.setStorVal sevm.currentTarget key value ∧ b'.logs = b.logs

variable {fs : List SFunc} {sevm : Sevm}

/-- The two setup reads under the selected access rules, in either gas lane. -/
theorem setup_access_inv (p : SysShape) {body : SFunc} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (access : sevm.benvStat.rules.access = .eip2929)
    (entry : fs[p.entryIdx]? = some (sysEntry p body))
    (run : SFunc.Run fs sevm (St b [] M G) (sysSetup p body) o) :
    ∃ b' G', b'.state = b.state ∧ b'.logs = b.logs ∧ SFunc.Run fs sevm
      (St b' [0, drainCount p.cap.word (b.getStorVal sevm.currentTarget 2) (b.getStorVal sevm.currentTarget 3),
        b.getStorVal sevm.currentTarget 2, b.getStorVal sevm.currentTarget 3] M G') (sysHeader p body) o := by
  have run := run.cut
  unfold sysSetup at run
  winv 2
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sloadA access step
  clear step
  winv 1
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sloadA access step
  clear step
  winv
  rw [afterSloadA_getStorVal, show Bytes.toB256 [0x02] = 2 from rfl,
    show Bytes.toB256 [0x03] = 3 from rfl] at run
  have state : (afterSloadA sevm (afterSloadA sevm b 3) 2).state = b.state := by
    rw [afterSloadA_state, afterSloadA_state]
  have logs : (afterSloadA sevm (afterSloadA sevm b 3) 2).logs = b.logs := by
    rw [afterSloadA_logs, afterSloadA_logs]
  generalize b.getStorVal sevm.currentTarget 2 = h at run ⊢
  generalize b.getStorVal sevm.currentTarget 3 = t at run ⊢
  rcases ric_branchTo List.not_mem_nil entry run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · have flag : B256.gtCheck p.cap.word (t - h) = 0 := flag
    winv 2 at run
    unfold sysEntry at run
    winv 2 at run
    have count : drainCount p.cap.word h t = p.cap.word := by
      unfold drainCount
      rw [ite_eq_right]
      intro over
      simp only [B256.gtCheck, over, ite_true] at flag
      exact absurd flag (by decide)
    exact ⟨_, _, state, logs, by rw [count]; exact run.uncut⟩
  · have flag : B256.gtCheck p.cap.word (t - h) ≠ 0 := flag
    unfold sysEntry at run
    winv 2 at run
    have count : drainCount p.cap.word h t = t - h := by
      unfold drainCount
      rw [ite_eq_left]
      by_contra over
      exact flag (by simp only [B256.gtCheck, over, ite_false])
    exact ⟨_, _, state, logs, by rw [count]; exact run.uncut⟩

/-- Actual pointer stores force a dynamic frame and retain the original word comparison. -/
theorem book_store_inv (p : SysShape) (stores : StoreInv sevm)
    {q : Devm} {c h t : B256} {M : Mem} {G : Nat} {o : Outcome}
    (entry : fs[p.excessIdx]? = some p.excessTree)
    (run : SFunc.Run fs sevm (St q [c, c, h, t] M G) (sysBook p) o) :
    sevm.isStatic = false ∧ ∃ q' G', q'.state = bookState q.state sevm.currentTarget h c t ∧
      q'.logs = q.logs ∧ SFunc.Run fs sevm (St q' [c] M G') p.excessTree o := by
  have run := run.cut
  unfold sysBook at run
  winv
  by_cases emptied : h + c = t
  · rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · simp only [B256.eqCheck, emptied, ite_true] at flag
      exact absurd flag (by decide)
    · unfold sysEmptied at run
      winv at run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨dynamic, q1, _, rfl, state1, logs1⟩ := stores step
      clear step
      winv at run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, q2, _, rfl, state2, logs2⟩ := stores step
      clear step
      refine ⟨dynamic, _, _, ?_, logs2.trans logs1, run.uncut⟩
      rw [state2, state1]
      simp only [bookState, emptied, ite_true]
      rfl
  · rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · unfold sysAdvance at run
      winv at run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨dynamic, q1, _, rfl, state, logs⟩ := stores step
      clear step
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil entry run
      refine ⟨dynamic, _, _, ?_, logs, run.uncut⟩
      rw [state]
      simp only [bookState, emptied, ite_false]
      rfl
    · have different : t ≠ h + c := fun same => emptied same.symm
      simp only [B256.eqCheck, different, ite_false] at flag
      exact absurd rfl flag

/-- The final actual stores and RETURN, under any store backend satisfying the callback. -/
theorem final_store_inv (len : PushWord) (stores : StoreInv sevm)
    {d post : Devm} {e c : B256} {M : Mem} {G : Nat}
    (run : SFunc.Run fs sevm (St d [e, c] M G) (sysFinal len) (.halted post)) :
    post.state = (d.state.setStorVal sevm.currentTarget 0 e).setStorVal sevm.currentTarget 1 0 ∧
      post.output = (M.read 0 (len.word * c).toNat).1 ∧ post.logs = d.logs := by
  have run := run.cut
  unfold sysFinal at run
  winv
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, d1, _, rfl, state1, logs1⟩ := stores step
  clear step
  winv
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, d2, _, rfl, state2, logs2⟩ := stores step
  clear step
  winv
  cases run with
  | last returned =>
    refine ⟨?_, (ri_return returned).1, ?_⟩
    · rw [ri_return_state returned, state2, state1]
      rfl
    · exact (ri_return returned).2.2.trans (logs2.trans logs1)

/-- The actual system-caller prefix stops at the runtime's own excess tree.
The record loop is the existing shared inversion, with no second induction. -/
theorem SysPath.prefix_inv {k : SysPath} (body : k.BodyInv sevm)
    (access : sevm.benvStat.rules.access = .eip2929) (stores : StoreInv sevm)
    (caller : sevm.caller = systemAddress) {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (run : SFunc.Run k.cert.prog sevm (St b [] M G)
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) o) :
    sevm.isStatic = false ∧ ∃ b' G',
      b'.state = bookState b.state sevm.currentTarget (SysPath.rd sevm b 2)
        (k.count sevm b) (SysPath.rd sevm b 3) ∧ b'.logs = b.logs ∧
      SFunc.Run k.cert.prog sevm
        (St b' [k.count sevm b]
          (k.memFold (SysPath.rd sevm b) (SysPath.rd sevm b 2) 0 (k.count sevm b).toNat M) G')
        k.shape.excessTree o := by
  obtain ⟨_, run⟩ := dispatch_system_inv caller run
  obtain ⟨b1, _, state1, logs1, run⟩ := setup_access_inv k.shape access k.entry run
  obtain ⟨b2, _, state2, logs2, run⟩ :=
    k.loop_inv body (k.count sevm b).toNat (index := 0) (Nat.zero_add _) run
  rw [getStorVal_eq_of_state state1] at run
  obtain ⟨dynamic, b3, _, state3, logs3, run⟩ := book_store_inv k.shape stores k.excessEntry run
  refine ⟨dynamic, b3, _, ?_, logs3.trans (logs2.trans logs1), run⟩
  rw [state3, state2, state1]

end Blanc.Lift.RequestSystem
