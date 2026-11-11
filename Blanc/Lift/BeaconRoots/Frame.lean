import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.RequestSystem.PathInv
import Blanc.Lift.WalkInvKit
import Blanc.Lift.EnvironmentInv

namespace Blanc.Lift.BeaconRoots

open Jaune Blanc.Lift
open Blanc.Lift.SystemExecution.BeaconRoots

variable {sevm : Sevm} {pre post b : Devm} {M : Mem} {G : Nat}

/-- Every successful ordinary read passes the actual length, nonzero and timestamp-tag guards. -/
theorem read_inv (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 (.halted post)) :
    sevm.data.length.toB256 = 32 ∧ Sevm.dataWord sevm 0 ≠ 0 ∧
      b.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0 ∧
      post.output = (b.getStorVal sevm.currentTarget
        ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256))).toBytes ∧
      post.state = b.state ∧ post.logs = b.logs := by
  have run := run.cut
  unfold t_001a_c0 at run
  winv
  rcases ric_branch run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · exact False.elim (run.false_of_noOk (by decide +kernel))
  · have length : sevm.data.length.toB256 = 32 := by
      by_cases h : sevm.data.length.toB256 = 32
      · exact h
      · simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl,
          B256.eqCheck, ite_eq_right h] at flag
        exact False.elim (flag rfl)
    unfold t_0024_c0 at run
    winv
    rcases ric_branch run with ⟨flag, _, run⟩ | ⟨_, _, run⟩
    · have nonzero : Sevm.dataWord sevm 0 ≠ 0 := by
        intro hz
        simp only [show Bytes.toB256 [] = (0 : B256) from rfl, hz, B256.eqCheck, ite_true] at flag
        exact (by decide : (1 : B256) ≠ 0) flag
      unfold t_002c_c0 at run
      winv
      obtain ⟨_, hd, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_sload fork.shanghaiOnwards hd
      clear hd
      winv
      rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, run⟩
      · exact False.elim (run.false_of_noOk (by decide +kernel))
      · have tag : b.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) =
            Sevm.dataWord sevm 0 := by
          change B256.eqCheck (b.getStorVal sevm.currentTarget
            (Sevm.dataWord sevm 0 % (0x1fff : B256))) (Sevm.dataWord sevm 0) ≠ 0 at flag
          by_cases h : b.getStorVal sevm.currentTarget
              (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0
          · exact h
          · simp only [B256.eqCheck, ite_eq_right h] at flag
            exact False.elim (flag rfl)
        unfold t_003c_c0 at run
        winv
        obtain ⟨_, hd, run⟩ := ric_next run
        obtain ⟨_, rfl⟩ := ri_sload fork.shanghaiOnwards hd
        clear hd
        winv
        cases run with
        | last hret =>
          refine ⟨length, nonzero, tag, ?_, ?_, ?_⟩
          · have hout := (ri_return hret).1
            simp only [show Bytes.toB256 [] = (0 : B256) from rfl,
              show (Bytes.toB256 [32]).toNat = 32 from rfl, B256.toNat_zero,
              afterSload_getStorVal] at hout
            have back := Mem.read_write_zero M (ys := (b.getStorVal sevm.currentTarget
              ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256))).toBytes)
              (by
                intro h
                have hn := congrArg List.length h
                simp only [B256.length_toBytes, List.length_nil] at hn
                omega)
            rw [B256.length_toBytes] at back
            exact hout.trans back
          · simpa only [RequestFee.afterSload_state] using RequestSystem.ri_return_state hret
          · simpa only [afterSload_logs] using (ri_return hret).2.2
    · exact False.elim (run.false_of_noOk (by decide +kernel))

/-- A successful ordinary frame has precisely the read arm's effects. -/
theorem exec_read (code : sevm.code = beaconRootsCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.data.length.toB256 = 32 ∧ Sevm.dataWord sevm 0 ≠ 0 ∧
      pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) = Sevm.dataWord sevm 0 ∧
      post.output = (pre.getStorVal sevm.currentTarget
        ((0x1fff : B256) + Sevm.dataWord sevm 0 % (0x1fff : B256))).toBytes ∧
      post.state = pre.state ∧ post.logs = pre.logs := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec cert_check code (progNoExec_of_all (by decide +kernel)) exec
  change some t_0000_c0 = some f at hf
  cases hf
  rw [St.self stack rfl] at run
  have run : SFunc.Run cert.prog sevm (St pre [] pre.memory pre.gasLeft)
      (RequestSystem.dispatchTree ⟨0x4d, [], by decide⟩ t_001a_c0 t_004d_c0) (.halted post) := run
  obtain ⟨_, run⟩ := RequestFee.dispatch_user_inv caller run
  exact read_inv fork run

/-- The successful system arm writes the two words, emits no logs, and preserves the old output. -/
theorem exec_system (code : sevm.code = beaconRootsCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller = systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧ post.state =
      (pre.state.setStorVal sevm.currentTarget (sevm.benvStat.time % (0x1fff : B256)) sevm.benvStat.time).setStorVal
        sevm.currentTarget ((0x1fff : B256) + sevm.benvStat.time % (0x1fff : B256)) (Sevm.dataWord sevm 0) ∧
      post.output = pre.output ∧ post.logs = pre.logs := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec cert_check code (progNoExec_of_all (by decide +kernel)) exec
  change some t_0000_c0 = some f at hf
  cases hf
  rw [St.self stack rfl] at run
  have run : SFunc.Run cert.prog sevm (St pre [] pre.memory pre.gasLeft)
      (RequestSystem.dispatchTree ⟨0x4d, [], by decide⟩ t_001a_c0 t_004d_c0) (.halted post) := run
  obtain ⟨_, run⟩ := RequestSystem.dispatch_system_inv caller run
  have run := run.cut
  unfold t_004d_c0 at run
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  have dynamic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
  clear hd
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
  clear hd
  cases run with
  | last hstop =>
    change Except.ok _ = Except.ok post at hstop
    cases hstop
    refine ⟨dynamic, ?_, ?_, ?_⟩
    · simp only [St_state, afterSstore_state]
      rfl
    · simp only [St, Devm.setMach_output, afterSstore_output]
    · simp only [St, Devm.setMach_logs, afterSstore_logs]

/-- A rejected timestamp/tag query cannot succeed, even with arbitrary old memory and value. -/
theorem exec_bad_guard (code : sevm.code = beaconRootsCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (fails : Sevm.dataWord sevm 0 = 0 ∨
      pre.getStorVal sevm.currentTarget (Sevm.dataWord sevm 0 % (0x1fff : B256)) ≠ Sevm.dataWord sevm 0) :
    IsEmpty (Exec 0 sevm pre (.ok post)) := by
  refine ⟨fun exec => ?_⟩
  obtain ⟨_, nonzero, tag, _⟩ := exec_read code fork stack caller exec
  exact fails.elim nonzero (fun mismatch => mismatch tag)

/-- The concrete 31-byte length control fails the actual CALLDATASIZE guard. -/
theorem exec_31_bytes (code : sevm.code = beaconRootsCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress) (length : sevm.data.length = 31) :
    IsEmpty (Exec 0 sevm pre (.ok post)) := by
  refine ⟨fun exec => ?_⟩
  have h := (exec_read code fork stack caller exec).1
  rw [length] at h
  exact (by decide : (Nat.toB256 31) ≠ 32) h

end Blanc.Lift.BeaconRoots
