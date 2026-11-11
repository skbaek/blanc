import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Lift.RequestSystem.PathInv
import Blanc.Lift.WalkInvKit
import Blanc.Lift.EnvironmentInv

/-! # Successful frames of the EIP-2935 runtime

Local bytecode classification, before transport through settled kept histories.
-/

namespace Blanc.Lift.HistoryStorage

open Jaune Blanc.Lift
open SystemExecution.HistoryStorage

theorem read_path {sevm : Sevm} {b post : Devm} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 (.halted post)) :
    sevm.data.length.toB256 = 32 ∧
    (Sevm.dataWord sevm 0).toNat ≤ (sevm.benvStat.number.toB256 - 1).toNat ∧
    (sevm.benvStat.number.toB256 - Sevm.dataWord sevm 0).toNat ≤ 8191 ∧
    ∃ G', SFunc.Run cert.prog sevm (St b [Sevm.dataWord sevm 0] M G')
      t_0036_c0 (.halted post) := by
  have run := run.cut
  unfold t_001a_c0 at run
  winv at run
  rcases ric_branch run with ⟨length, _, run⟩ | ⟨_, _, run⟩
  swap
  · exact (run.false_of_noOk (by decide)).elim
  have length : sevm.data.length.toB256 = 32 := by
    have h := congrArg (fun x : B256 => x + 32) length
    change sevm.data.length.toB256 - 32 + 32 = 0 + 32 at h
    rw [B256.sub_add_cancel] at h
    exact h
  unfold t_0021_c0 at run
  winv at run
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_number hd
  clear hd
  winv at run
  rcases ric_branch run with ⟨upper, _, run⟩ | ⟨_, _, run⟩
  swap
  · exact (run.false_of_noOk (by decide)).elim
  unfold t_002c_c0 at run
  winv at run
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_number hd
  clear hd
  winv at run
  rcases ric_branch run with ⟨lower, _, run⟩ | ⟨_, _, run⟩
  · exact ⟨length, toNat_le_of_gtCheck_eq_zero upper,
      toNat_le_of_gtCheck_eq_zero lower, _, run.uncut⟩
  · exact (run.false_of_noOk (by decide)).elim

theorem exec_read_path {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = historyStorageCode) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    sevm.data.length.toB256 = 32 ∧
    (Sevm.dataWord sevm 0).toNat ≤ (sevm.benvStat.number.toB256 - 1).toNat ∧
    (sevm.benvStat.number.toB256 - Sevm.dataWord sevm 0).toNat ≤ 8191 ∧
    ∃ G', SFunc.Run cert.prog sevm (St pre [Sevm.dataWord sevm 0] pre.memory G')
      t_0036_c0 (.halted post) := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec cert_check code (progNoExec_of_all (by decide)) exec
  change some t_0000_c0 = some f at hf
  cases hf
  rw [St.self stack rfl] at run
  obtain ⟨_, run⟩ := RequestFee.dispatch_user_inv
    (dest := ⟨0x46, [], by decide⟩) caller run
  exact read_path run

theorem read_tail_inv {sevm : Sevm} {b post : Devm} {M : Mem} {G : Nat} {q : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [q] M G) t_0036_c0 (.halted post)) :
    post.output = (b.getStorVal sevm.currentTarget (q % 8191)).toBytes ∧
    post.state = b.state ∧ post.logs = b.logs := by
  have run := run.cut
  unfold t_0036_c0 at run
  winv at run
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork.shanghaiOnwards hd
  clear hd
  winv at run
  cases run with
  | last h =>
    obtain ⟨output, _, logs⟩ := ri_return h
    refine ⟨?_, (RequestSystem.ri_return_state h).trans (RequestFee.afterSload_state _ _ _), ?_⟩
    · change post.output = ((M.write 0 (b.getStorVal sevm.currentTarget (q % 8191)).toBytes).read 0 32).1 at output
      have readback := Mem.read_write_zero M
        (ys := (b.getStorVal sevm.currentTarget (q % 8191)).toBytes)
        (List.ne_nil_of_length_pos (by rw [B256.length_toBytes]; decide))
      rw [B256.length_toBytes] at readback
      exact output.trans readback
    · exact logs.trans (afterSload_logs _ _ _)

theorem system_inv {sevm : Sevm} {b post : Devm} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_0046_c0 (.halted post)) :
    sevm.isStatic = false ∧
    post.state = b.state.setStorVal sevm.currentTarget
      ((sevm.benvStat.number.toB256 - 1) % 8191) (Sevm.dataWord sevm 0) ∧
    post.output = b.output ∧ post.logs = b.logs := by
  have run := run.cut
  unfold t_0046_c0 at run
  winv at run
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_number hd
  clear hd
  winv at run
  obtain ⟨_, hd, run⟩ := ric_next run
  have static := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
  clear hd
  cases run with
  | last h =>
    change Except.ok _ = Except.ok post at h
    cases h
    exact ⟨static, afterSstore_state _ _ _ _, afterSstore_output _ _ _ _, afterSstore_logs _ _ _ _⟩

theorem exec_system_frame {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = historyStorageCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller = systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧
    post.state = pre.state.setStorVal sevm.currentTarget
      ((sevm.benvStat.number.toB256 - 1) % 8191) (Sevm.dataWord sevm 0) ∧
    post.output = pre.output ∧ post.logs = pre.logs := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec cert_check code (progNoExec_of_all (by decide)) exec
  change some t_0000_c0 = some f at hf
  cases hf
  rw [St.self stack rfl] at run
  obtain ⟨_, run⟩ := RequestSystem.dispatch_system_inv
    (dest := ⟨0x46, [], by decide⟩) caller run
  exact system_inv fork run

theorem exec_read_frame {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = historyStorageCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (lengthBound : sevm.data.length < 2 ^ 256)
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    sevm.data.length = 32 ∧
    (Sevm.dataWord sevm 0).toNat ≤ (sevm.benvStat.number.toB256 - 1).toNat ∧
    (sevm.benvStat.number.toB256 - Sevm.dataWord sevm 0).toNat ≤ 8191 ∧
    post.output = (pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % 8191)).toBytes ∧
    post.state = pre.state ∧ post.logs = pre.logs := by
  obtain ⟨length, upper, lower, _, run⟩ := exec_read_path code stack caller exec
  have literal := congrArg B256.toNat length
  rw [B256.toNat_toB256_of_lt lengthBound] at literal
  exact ⟨literal, upper, lower, read_tail_inv fork run⟩

end Blanc.Lift.HistoryStorage
