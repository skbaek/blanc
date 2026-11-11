import Blanc.Lift.ConsolidationRequest.System
import Blanc.Lift.RequestSystem.PathInv

/-!
# Every successful EIP-7251 system frame

The converse of `system_call_ok` at frame level, from any frame at the system caller with an empty stack and
well-formed memory: whatever storage, memory contents, calldata, value and gas it starts with, a successful run
of the canonical bytes ends in `sysState` and returns the drained records. The runtime's system arm reads neither calldata nor `CALLVALUE`, so neither
matters. The trees are inverted by the shared `RequestSystem.SysPath.exec_frame_inv`; here are the record body's
inversion (`system_body_inv`) and the plain excess arm's (`system_excessInv`).

* `exec_system_frame`: the frame is non-static, its post state is `sysState`, and on well-formed memory it
  returns `drained` of the storage it started with, `min(2, tail - head)` records of 116 bytes (counted in
  words, as the bytes count).
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open RequestSystem
open SystemExecution.ConsolidationRequest (cert t_00f1_c1)
open SystemExecution.ConsolidationRequest.Amsterdam (sysPath sysShape sysWords sysMemory recordKey recordStage
  off0 off1 off2 off3 entry6)

variable {sevm : Sevm}

/-- **The record body, inverted.** A successful run of the body reads the record's four words, writes them
over the record's window, and re-enters the loop header at the next index; the world state is unchanged. -/
theorem system_body_inv (fork : ShanghaiOnwards sevm.benvStat.fork) : sysPath.BodyInv sevm := by
  intro b M G i c h t o run
  have run : SFunc.RunCut cert.prog sevm [] (St b [i, c, h, t] M G) t_00f1_c1 (.done o) := run.cut
  unfold t_00f1_c1 at run
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  obtain ⟨_, run⟩ := ric_jump List.not_mem_nil entry6 run
  simp only [afterSload_getStorVal] at run
  rw [show Bytes.toB256 [4] = 4 from rfl, show Bytes.toB256 [116] = 116 from rfl,
    show Bytes.toB256 [1] = 1 from rfl, show Bytes.toB256 [2] = 2 from rfl, show Bytes.toB256 [3] = 3 from rfl,
    show Bytes.toB256 [20] = 20 from rfl, show Bytes.toB256 [32] = 32 from rfl,
    show (Bytes.toB256 [96]).toNat = 96 by decide] at run
  exact ⟨_, _, by simp only [RequestFee.afterSload_state], by simp only [afterSload_logs], run.uncut⟩

/-- **The excess arm, inverted**: the plain arm with target 1. -/
theorem system_excessInv (fork : ShanghaiOnwards sevm.benvStat.fork) : sysPath.ExcessInv sevm := by
  intro d M G c o run
  have hover : cert.prog[3]? = some (plainOver sysWords) := rfl
  have hfinal : cert.prog[4]? = some (sysFinal sysWords.len) := rfl
  have run : SFunc.Run cert.prog sevm (St d [c] M G) (plainExcess sysWords) o := run
  rw [show sysPath.shape.next = plainNext sysWords.target.word from rfl,
    show sysPath.shape.len = sysWords.len from rfl, show sysPath.cert.prog = cert.prog from rfl]
  exact excess_inv sysWords fork hover hfinal run

variable {pre post : Devm}

/-- **Every successful EIP-7251 system frame.** A successful execution of the canonical bytes at the system
caller, on a covered fork, from an empty stack and well-formed memory, with any calldata, value and gas: the
frame is non-static, its post state is `sysState` (pointers, excess and count as the bytes define, nothing
else), and it returns the drained records of the storage it started with. -/
theorem exec_system_frame (hcode : sevm.code = consolidationRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (wf : Mem.Wf pre.memory) (caller : sevm.caller = systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧ post.state = sysState sysShape pre.state sevm.currentTarget ∧
      post.output = drained (pre.getStorVal sevm.currentTarget) ∧ post.logs = pre.logs := by
  obtain ⟨static, hstate, hout, hlogs⟩ := SysPath.exec_frame_inv (k := sysPath) (system_body_inv fork.shanghaiOnwards)
    (system_excessInv fork.shanghaiOnwards) hcode fork caller stack exec
  exact ⟨static, hstate, hout.trans (sysOutput.frame_inv_output sevm pre wf), hlogs⟩

end Blanc.Lift.ConsolidationRequest
