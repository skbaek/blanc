import Blanc.Lift.BuilderRequest.FeePath
import Blanc.SystemCallForward

/-!
# What the builder contracts' submissions share

Both submissions bump the count in slot 1, read the tail in slot 3, write their record, emit a topicless
`LOG0`, bump the tail and `STOP`; and a successful user frame at either runtime is at the submission's
length or an empty-calldata fee read. These are statements about the code's walk over any storage, on a
fork's `StorageSteps`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- The count word the path reads. -/
def countWord (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 1

/-- `LOG0`, bump the tail, `STOP`. -/
def logTail : SFunc :=
  (.next (.reg (.log 0)) (.next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push [0x03] (by decide)) (.next (.reg .sstore) (.last .stop))))))

/-- A `LOG0` of memory `0 .. n`'s bytes, at the executing address. -/
def windowLog (sevm : Sevm) (M : Mem) (n : Nat) : Log :=
  ⟨sevm.currentTarget, [], (M.read 0 n).1⟩

/-- `LOG0` of a window, with its expansion charged. -/
def log0Gas (M : Mem) (n : Nat) : Nat :=
  gLog + gLogdata * n + gLogtopic * 0 +
    (calculateMemoryGasCost (memExtSize M.size 0 n) - calculateMemoryGasCost M.size)

namespace StorageSteps

variable {sevm : Sevm} (l : StorageSteps sevm)

/-- After the count bump. -/
def countStore (b : Devm) : Devm := l.afterWrite (l.afterRead b 1) 1 (1 + countWord sevm b)

/-- The tail word the path reads, after the count bump. -/
def tailWord (b : Devm) : B256 := (l.countStore b).getStorVal sevm.currentTarget 3

/-- After reading the tail. -/
def tailRead (b : Devm) : Devm := l.afterRead (l.countStore b) 3

variable {l} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

theorem Valid.logTail_inv {fs : List SFunc} {n tail : B256} (v : l.Valid)
    (run : SFunc.RunCut fs sevm [] (St b [0, n, tail] M G) logTail (.done o)) :
    ∃ G', o = .halted (St (l.afterWrite (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)) []
      (M.read 0 n.toNat).2 G') := by
  unfold logTail at run
  obtain ⟨d, h, run⟩ := ric_next run
  rcases of_run_reg h with ⟨pc, raw⟩
  simp only [Rinst.run, Rinst.runCore] at raw
  rw [show (St b [0, n, tail] M G).popToNat = .ok (0, St b [n, tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St b [n, tail] M G).popToNat = .ok (n.toNat, St b [tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St b [tail] M G).popN ((0 : Fin 5) : Nat) = .ok ([], St b [tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rcases Except.bind_eq_ok raw with ⟨s1, hcharge, rest⟩
  rcases Except.bind_eq_ok rest with ⟨_, -, last⟩
  cases last
  have eqGas := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)
  have eqSt : s1 = St b [tail] M s1.gasLeft := eqGas
  rw [eqSt] at run
  simp only [St.memRead_fst, St.memRead_snd] at run
  change SFunc.RunCut _ _ _ (St (b.addLog (windowLog sevm M n.toNat)) [tail]
    (M.read 0 n.toNat).2 s1.gasLeft) _ _ at run
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.writeInv h
  cases run with
  | last terminal =>
    change Except.ok _ = Except.ok _ at terminal
    cases terminal
    exact ⟨_, rfl⟩

/-- `LOG0`, bump the tail, `STOP`, forward. -/
theorem Valid.logTail_exact {fs : List SFunc} {n tail : B256} (v : l.Valid)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact fs sevm
      (St b [0, n, tail] M
        (G + l.writeCharge (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat))
      logTail
      (.halted (St (l.afterWrite (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)) []
        (M.read 0 n.toNat).2 (G + l.writeRepay (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)))) := by
  have emitted : Ninst.RunCompiled sevm
      (St b [0, n, tail] M
        (G + l.writeCharge (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat)) (.reg (.log 0))
      (St (b.addLog (windowLog sevm M n.toNat)) [tail] (M.read 0 n.toNat).2
        (G + l.writeCharge (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := n) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  unfold logTail
  refine .next emitted ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine v.writeRun dynamic (by omega) ?_
  exact .last rfl

/-- The count bump's state. -/
theorem Valid.countStore_state (v : l.Valid) (b : Devm) :
    (l.countStore b).state =
      b.state.setStorVal sevm.currentTarget 1 (1 + b.getStorVal sevm.currentTarget 1) := by
  rw [countStore, v.writeState, v.readState]
  rfl

theorem Valid.tailWord_eq (v : l.Valid) (b : Devm) :
    l.tailWord b = b.getStorVal sevm.currentTarget 3 := by
  show ((l.countStore b).state.getStor sevm.currentTarget).get 3 =
    (b.state.getStor sevm.currentTarget).get 3
  rw [v.countStore_state, State.getStor_setStorVal_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]

theorem Valid.read_feeBase (v : l.Valid) (key : B256) (a : Adr) (s : Devm) :
    (l.feeBase s).getStorVal a key = s.getStorVal a key := by
  rw [feeBase, v.getStorVal_read, v.getStorVal_read]

theorem Valid.state_feeBase (v : l.Valid) (s : Devm) : (l.feeBase s).state = s.state := by
  rw [feeBase, v.readState, v.readState]

end StorageSteps

theorem addLog_output (w : Devm) (l : Log) : (w.addLog l).output = w.output := rfl

namespace UserPath

variable {k : UserPath} {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}

/-- **The fork of a user frame.** A successful execution at a non-system caller from an empty stack passes
the guard, quotes the fee, and either reaches the submission arm at the submission's length, or is a fee read
on empty calldata. `lengthBound` holds of any calldata a frame can carry, since `CALLDATASIZE` is read as a
word. -/
theorem exec_user_cases (v : l.Valid) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    (pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧ sevm.data.length = k.shape.len.word.toNat ∧
      ∃ iterations finalOutput,
        WordFakeExponential.Run (storedExcess k.shape.target.word sevm pre) 17 1 17 0 iterations
          finalOutput ∧
        ∃ G0, SFunc.Run k.cert.prog sevm (St (l.feeBase pre) [finalOutput / (17 : B256)] pre.memory G0)
          k.submission (.halted post)) ∨
    (sevm.data = [] ∧ ∃ iterations finalOutput, FeeReadOn l k.target pre post iterations finalOutput) := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, G0, run⟩ :=
    feePath_inv k.shape v k.revert_noOk k.window k.loop run
  by_cases hword : sevm.data.length.toB256 = k.shape.len.word
  · left
    have literal : sevm.data.length = k.shape.len.word.toNat := by
      have values := congrArg B256.toNat hword
      rwa [B256.toNat_toB256_of_lt lengthBound] at values
    rw [RequestFee.selected, ite_eq_left hword] at run
    exact ⟨active, literal, iterations, finalOutput, wordRun, G0, run⟩
  · right
    rw [RequestFee.selected, ite_eq_right hword] at run
    obtain ⟨empty, _, _⟩ := RequestFee.guard_inv k.getterRevert_noOk run
    have literal : sevm.data = [] := by
      have values := congrArg B256.toNat empty
      rw [B256.toNat_toB256_of_lt lengthBound] at values
      exact List.eq_nil_of_length_eq_zero values
    exact ⟨literal, exec_fee_read v hcode stack aligned wf caller literal exec⟩

end UserPath

/-- A builder contract's user frames: its code, what a successful non-system frame there is on a fork's steps,
and that every such frame is one. -/
structure UserFrames where
  /-- The runtime bytes. -/
  code : ByteArray
  /-- A successful non-system frame on a fork's steps: a submission or a fee read. -/
  Frame : ∀ {sevm : Sevm}, StorageSteps sevm → Devm → Devm → Prop
  frame : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}, l.Valid → sevm.code = code →
    pre.stack = [] → pre.memory.size % 32 = 0 → Mem.Wf pre.memory → sevm.data.length < 2 ^ 256 →
    sevm.caller ≠ systemAddress → Exec 0 sevm pre (.ok post) → Frame l pre post

/-- **Builder frames, under covered forks.** Every successful execution of the contract's code at a non-system
caller, from an empty stack, is a submission or a fee read. `aligned` and `wf` hold of the empty memory every
frame starts with; `lengthBound` holds of any calldata a frame can carry, since `CALLDATASIZE` is read as a word.
Success already implies slot 0 is off the inhibitor. The statement stops at the frame: it does not cover message
or transaction level. -/
theorem UserFrames.exec_user_frame (c : UserFrames) {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = c.code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0)
    (wf : Mem.Wf pre.memory) (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : c.Frame (coveredSteps sevm) pre post :=
  c.frame (coveredSteps_valid fork) hcode stack aligned wf lengthBound caller exec

/-- At excess 0 the fee recurrence takes one step and quotes 1 wei. -/
theorem quote_zero_excess : WordFakeExponential.Run 0 17 1 17 0 1 17 := by
  have next : WordFakeExponential.nextAccumulator 0 17 1 17 = 0 := by decide
  have sum : (0 : B256) + 17 = 17 := by decide
  refine .step (by decide) ?_
  rw [next, sum]
  exact .stop _ _

end Blanc.Lift.BuilderRequest
