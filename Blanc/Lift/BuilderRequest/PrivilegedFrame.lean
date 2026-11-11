import Blanc.Lift.RequestSystem.PrivilegedInv
import Blanc.Lift.BuilderRequest.UserFrameAmsterdam
import Blanc.Lift.BuilderRequest.Deposit.Fifo
import Blanc.Lift.BuilderRequest.Exit.Fifo
import Blanc.Lift.BuilderRequest.Latch

/-! Original successful SYSTEM-caller frames, on either storage-gas backend.
The inverse keeps arbitrary dirty/warm state and well-formed memory, and follows
the actual calldata branch rather than assuming a scheduled system message. -/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestSystem
open RequestFee (PushWord)

variable {sevm : Sevm} {l : StorageSteps sevm}

theorem StorageSteps.Valid.storeInv (v : l.Valid) : StoreInv sevm := by
  intro b d S M G key value step
  have dynamic := v.writeDynamic step
  obtain ⟨G', rfl⟩ := v.writeInv step
  exact ⟨dynamic, _, G', rfl, v.writeState _ _ _, v.writeLogs _ _ _⟩

section Excess

variable (p : LatchWords) {fs : List SFunc}

private theorem over_inv {d : Devm} {x y c : B256} {M : Mem} {G : Nat} {o : Outcome}
    (final : fs[5]? = some (sysFinal p.len))
    (run : SFunc.Run fs sevm (St d [x, y, c] M G) (sysOver p) o) :
    ∃ G', SFunc.Run fs sevm
      (St d [if x + y > p.target.word then (x + y) - p.target.word else 0, c] M G')
      (sysFinal p.len) o := by
  replace run := run.cut
  unfold sysOver at run
  winv
  by_cases over : x + y > p.target.word
  · rw [ite_eq_left over]
    rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · simp only [B256.gtCheck, over, ite_true] at flag
      exact absurd flag (by decide)
    · unfold sysCarry at run
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil final run
      exact ⟨_, run.uncut⟩
  · rw [ite_eq_right over]
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · unfold sysNoCarry at run
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil final run
      exact ⟨_, run.uncut⟩
    · simp only [B256.gtCheck, over, ite_false] at flag
      exact absurd rfl flag

private theorem read_excess_inv (v : l.Valid) {d : Devm} {c : B256} {M : Mem} {G : Nat} {o : Outcome}
    (noCarry : fs[4]? = some (sysNoCarry p)) (final : fs[5]? = some (sysFinal p.len))
    (run : SFunc.Run fs sevm (St d [c] M G) (sysRead p) o) :
    ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run fs sevm
      (St d' [excessNext p.target.word (d.getStorVal sevm.currentTarget 0)
        (d.getStorVal sevm.currentTarget 1), c] M G') (sysFinal p.len) o := by
  replace run := run.cut
  unfold sysRead at run
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  simp only [v.getStorVal_read] at run
  rw [inhibitor_push, show Bytes.toB256 [] = 0 from rfl,
    show Bytes.toB256 [0x01] = 1 from rfl] at run
  have state : (l.afterRead (l.afterRead d 0) 1).state = d.state := by
    rw [v.readState, v.readState]
  have logs : (l.afterRead (l.afterRead d 0) 1).logs = d.logs := by
    rw [v.readLogs, v.readLogs]
  generalize he : d.getStorVal sevm.currentTarget 0 = e at run ⊢
  generalize hn : d.getStorVal sevm.currentTarget 1 = n at run ⊢
  by_cases inhibitor : B256.max = e
  · simp only [excessNext, inhibitor, ite_true]
    rcases ric_branchTo List.not_mem_nil noCarry run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · simp only [B256.eqCheck, inhibitor, ite_true] at flag
      exact absurd flag (by decide)
    · unfold sysNoCarry at run
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil final run
      exact ⟨_, _, state, logs, run.uncut⟩
  · simp only [excessNext, inhibitor, ite_false]
    rcases ric_branchTo List.not_mem_nil noCarry run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · obtain ⟨_, run⟩ := over_inv p final run.uncut
      exact ⟨_, _, state, logs, run⟩
    · simp only [B256.eqCheck, inhibitor, ite_false] at flag
      exact absurd rfl flag

/-- The original calldata word selects either the empty-data excess update or the inhibitor. -/
theorem privileged_excess_inv (v : l.Valid)
    {d : Devm} {c : B256} {M : Mem} {G : Nat} {o : Outcome}
    (noCarry : fs[4]? = some (sysNoCarry p)) (final : fs[5]? = some (sysFinal p.len))
    (lengthBound : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run fs sevm (St d [c] M G) (sysExcess p) o) :
    ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run fs sevm
      (St d' [if sevm.data = [] then
          excessNext p.target.word (d.getStorVal sevm.currentTarget 0) (d.getStorVal sevm.currentTarget 1)
        else B256.max, c] M G') (sysFinal p.len) o := by
  replace run := run.cut
  unfold sysExcess at run
  winv
  rcases ric_branch run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · have empty : sevm.data = [] := by
      have word := congrArg B256.toNat flag
      rw [B256.toNat_toB256_of_lt lengthBound] at word
      exact List.eq_nil_of_length_eq_zero word
    rw [ite_eq_left empty]
    exact read_excess_inv p v noCarry final run.uncut
  · have nonempty : sevm.data ≠ [] := by
      intro empty
      rw [empty] at flag
      exact flag rfl
    rw [ite_eq_right nonempty]
    unfold sysLatch at run
    winv 2 at run
    rw [inhibitor_push] at run
    exact ⟨d, _, rfl, rfl, run.uncut⟩

end Excess

namespace Deposit

/-- The actual six-read/fourteen-write record body, inverted under the selected rules. -/
theorem privileged_body_inv (v : l.Valid) : sysPath.BodyInv sevm := by
  intro b M G i c h t o run
  replace run := run.cut
  change SFunc.RunCut cert.prog sevm [] (St b [i, c, h, t] M G) t_013b_c2 (.done o) at run
  unfold t_013b_c2 at run
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  obtain ⟨_, run⟩ := ric_jump List.not_mem_nil entry7 run
  simp only [v.getStorVal_read] at run
  rw [show Bytes.toB256 [4] = (4 : B256) from rfl,
    show Bytes.toB256 [6] = (6 : B256) from rfl,
    show Bytes.toB256 [184] = (184 : B256) from rfl,
    show Bytes.toB256 [1] = (1 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl,
    show Bytes.toB256 [2] = (2 : B256) from rfl,
    show Bytes.toB256 [64] = (64 : B256) from rfl,
    show Bytes.toB256 [16] = (16 : B256) from rfl,
    show Bytes.toB256 [7] = (7 : B256) from rfl,
    show Bytes.toB256 [56] = (56 : B256) from rfl,
    show Bytes.toB256 [48] = (48 : B256) from rfl,
    show Bytes.toB256 [5] = (5 : B256) from rfl,
    show Bytes.toB256 [40] = (40 : B256) from rfl,
    show Bytes.toB256 [3] = (3 : B256) from rfl,
    show Bytes.toB256 [24] = (24 : B256) from rfl,
    show Bytes.toB256 [8] = (8 : B256) from rfl] at run
  simp only [show (64 : B256).toNat = 64 from rfl, show (56 : B256).toNat = 56 from rfl,
    show (48 : B256).toNat = 48 from rfl, show (40 : B256).toNat = 40 from rfl,
    show (32 : B256).toNat = 32 from rfl, show (24 : B256).toNat = 24 from rfl,
    show (16 : B256).toNat = 16 from rfl, show (8 : B256).toNat = 8 from rfl] at run
  change ∃ b' G', b'.state = b.state ∧ b'.logs = b.logs ∧ SFunc.Run cert.prog sevm
    (St b' [1 + i, c, h, t] ((recordStage (b.getStorVal sevm.currentTarget) h i).applyMemory M) G')
    (sysHeader sysShape t_013b_c2) o
  simp only [recordStage, MemoryStage.applyMemory, List.foldl]
  dsimp only [off0, off1, off2, off3, off4, off5, amountAt, amountOf, recordKey]
  refine ⟨_, _, ?_, ?_, run.uncut⟩
  · simp only [v.readState]
  · simp only [v.readLogs]

end Deposit

namespace Exit

/-- The actual source-address/word record body, inverted under the selected rules. -/
theorem privileged_body_inv (v : l.Valid) : sysPath.BodyInv sevm := by
  intro b M G i c h t o run
  replace run := run.cut
  change SFunc.RunCut cert.prog sevm [] (St b [i, c, h, t] M G) t_00ff_c2 (.done o) at run
  unfold t_00ff_c2 at run
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  replace run := ric_next run
  obtain ⟨_, step, run⟩ := run
  obtain ⟨_, rfl⟩ := v.readInv step
  clear step
  winv
  obtain ⟨_, run⟩ := ric_jump List.not_mem_nil entry7 run
  simp only [v.getStorVal_read] at run
  rw [show Bytes.toB256 [4] = (4 : B256) from rfl,
    show Bytes.toB256 [3] = (3 : B256) from rfl,
    show Bytes.toB256 [68] = (68 : B256) from rfl,
    show Bytes.toB256 [1] = (1 : B256) from rfl,
    show Bytes.toB256 [20] = (20 : B256) from rfl,
    show Bytes.toB256 [32] = (32 : B256) from rfl,
    show Bytes.toB256 [2] = (2 : B256) from rfl] at run
  refine ⟨_, _, ?_, ?_, run.uncut⟩
  · simp only [v.readState]
  · simp only [v.readLogs]

end Exit

/-- A canonical builder system path, with its actual record-body inverse and excess entries. -/
structure PrivilegedPath where
  path : SysPath
  words : LatchWords
  memory : SysMemory path
  output : SysOutput path memory
  tree : path.shape.excessTree = sysExcess words
  len : words.len = path.shape.len
  next : path.shape.next = excessNext words.target.word
  noCarry : path.cert.prog[4]? = some (sysNoCarry words)
  final : path.cert.prog[5]? = some (sysFinal words.len)
  body : ∀ {sevm : Sevm} {l : StorageSteps sevm}, l.Valid → path.BodyInv sevm

namespace PrivilegedPath

/-- The exact privileged effects, with the original calldata deciding the reversible latch. -/
def Frame (k : PrivilegedPath) (sevm : Sevm) (pre post : Devm) : Prop :=
  sevm.isStatic = false ∧
  post.state = (if sevm.data = [] then sysState k.path.shape pre.state sevm.currentTarget
    else latchState k.path.shape pre.state sevm.currentTarget) ∧
  post.output = k.output.drained (pre.getStorVal sevm.currentTarget) (pre.getStorVal sevm.currentTarget 2)
    (drainCount k.path.shape.cap.word (pre.getStorVal sevm.currentTarget 2)
      (pre.getStorVal sevm.currentTarget 3)).toNat ∧
  (∀ a, post.getBal a = pre.getBal a) ∧ post.logs = pre.logs

private theorem exec_on (k : PrivilegedPath) (v : l.Valid)
    {pre post : Devm} (runtime : sevm.code = k.path.code)
    (access : sevm.benvStat.rules.access = .eip2929)
    (stack : pre.stack = []) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller = systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : k.Frame sevm pre post := by
  obtain ⟨f, root, run⟩ := lift_sound_noExec k.path.check runtime k.path.noExec exec
  rw [k.path.root] at root
  cases root
  rw [St.self stack rfl] at run
  obtain ⟨dynamic, b1, _, state1, logs1, run⟩ := k.path.prefix_inv (k.body v) access v.storeInv caller run
  rw [k.tree] at run
  obtain ⟨b2, _, state2, logs2, run⟩ := privileged_excess_inv k.words v k.noCarry k.final lengthBound run
  obtain ⟨state, output, logs⟩ := final_store_inv k.words.len v.storeInv run
  have metadata : ∀ key : B256, key.toNat ≤ 1 →
      b1.getStorVal sevm.currentTarget key = pre.getStorVal sevm.currentTarget key := by
    intro key small
    rw [SysPath.getStorVal_of_state state1, bookState]
    have different : ∀ x : B256, 2 ≤ x.toNat → x ≠ key := fun x big same => by rw [same] at big; omega
    split
    · rw [State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (different 3 (by decide)),
        State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (different 2 (by decide))]
      rfl
    · rw [State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (different 2 (by decide))]
      rfl
  rw [state2, state1, metadata 0 (by decide), metadata 1 (by decide)] at state
  have world : post.state =
      (if sevm.data = [] then sysState k.path.shape pre.state sevm.currentTarget
       else latchState k.path.shape pre.state sevm.currentTarget) := by
    by_cases empty : sevm.data = []
    · rw [ite_eq_left empty] at state ⊢
      simp only [sysState, k.next]
      exact state
    · rw [ite_eq_right empty] at state ⊢
      exact state
  refine ⟨dynamic, world, ?_, ?_, logs.trans (logs2.trans logs1)⟩
  · rw [k.len] at output
    exact output.trans (k.output.frame_inv_output sevm pre wf)
  · intro a
    change (post.state.get a).bal = (pre.state.get a).bal
    rw [world]
    split
    · exact sysState_bal _ _ _ _
    · exact latchState_bal _ _ _ _

/-- Every original successful privileged frame, under covered forks or Amsterdam.
The backend callback is discharged here; no readiness or state-gas assumption escapes. -/
theorem exec_frame (k : PrivilegedPath) {pre post : Devm}
    (runtime : sevm.code = k.path.code)
    (fork : CoveredFork sevm.benvStat.fork ∨ sevm.benvStat.fork = .amsterdam)
    (stack : pre.stack = []) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller = systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : k.Frame sevm pre post := by
  rcases fork with covered | amsterdam
  · exact k.exec_on (coveredSteps_valid covered) runtime covered.rules_access stack wf lengthBound caller exec
  · exact k.exec_on (amsterdamSteps_valid amsterdam) runtime (amsterdam_access amsterdam)
      stack wf lengthBound caller exec

end PrivilegedPath

/-- Deposit's canonical path; every proof field is discharged by its actual bytes. -/
def Deposit.privilegedPath : PrivilegedPath where
  path := Deposit.sysPath
  words := Deposit.sysWords
  memory := Deposit.sysMemory
  output := Deposit.sysOutput
  tree := rfl
  len := rfl
  next := rfl
  noCarry := rfl
  final := rfl
  body := Deposit.privileged_body_inv

/-- Exit's canonical path, sharing the same privileged inverse. -/
def Exit.privilegedPath : PrivilegedPath where
  path := Exit.sysPath
  words := Exit.sysWords
  memory := Exit.sysMemory
  output := Exit.sysOutput
  tree := rfl
  len := rfl
  next := rfl
  noCarry := rfl
  final := rfl
  body := Exit.privileged_body_inv

end Blanc.Lift.BuilderRequest
