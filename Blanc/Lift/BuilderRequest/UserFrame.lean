import Blanc.Lift.BuilderRequest.FeePath

/-!
# What the builder contracts' submissions share

Both submissions bump the count in slot 1, read the tail in slot 3, write their record, emit a topicless
`LOG0`, bump the tail and `STOP`; and a successful user frame at either runtime is at the submission's
length or an empty-calldata fee read. These are statements about the code's walk over any storage, under
covered forks.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

section Tail

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- The count word the path reads. -/
def countWord (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 1

/-- After the count bump. -/
def countStore (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 1) 1 (1 + countWord sevm b)

/-- The tail word the path reads, after the count bump. -/
def tailWord (sevm : Sevm) (b : Devm) : B256 := (countStore sevm b).getStorVal sevm.currentTarget 3

/-- After reading the tail. -/
def tailRead (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (countStore sevm b) 3

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

theorem logTail_inv {fs : List SFunc} {n tail : B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm [] (St b [0, n, tail] M G) logTail (.done o)) :
    ∃ G', o = .halted (St (afterSstore sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)) []
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
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  cases run with
  | last terminal =>
    change Except.ok _ = Except.ok _ at terminal
    cases terminal
    exact ⟨_, rfl⟩

theorem logTail_exact {fs : List SFunc} {n tail : B256} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact fs sevm
      (St b [0, n, tail] M
        (G + sstoreCost sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat))
      logTail
      (.halted (St (afterSstore sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail)) []
        (M.read 0 n.toNat).2 G)) := by
  have emitted : Ninst.RunCompiled sevm
      (St b [0, n, tail] M
        (G + sstoreCost sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3 +
          log0Gas M n.toNat)) (.reg (.log 0))
      (St (b.addLog (windowLog sevm M n.toNat)) [tail] (M.read 0 n.toNat).2
        (G + sstoreCost sevm (b.addLog (windowLog sevm M n.toNat)) 3 (1 + tail) + 3 + 3 + 3)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := n) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  unfold logTail
  refine .next emitted ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  exact .last rfl

theorem tailWord_eq (sevm : Sevm) (s : Devm) :
    tailWord sevm s = s.getStorVal sevm.currentTarget 3 := by
  change (Devm.getStor (countStore sevm s) sevm.currentTarget).get 3 =
    (Devm.getStor s sevm.currentTarget).get 3
  rw [countStore, afterSstore_getStor_self, afterSload_getStor,
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]

theorem read_feeBase (sevm : Sevm) (key : B256) (a : Adr) (s : Devm) :
    (feeBase sevm s).getStorVal a key = s.getStorVal a key := by
  rw [feeBase, afterSload_getStorVal, afterSload_getStorVal]

theorem countWord_feeBase (sevm : Sevm) (s : Devm) :
    countWord sevm (feeBase sevm s) = s.getStorVal sevm.currentTarget 1 :=
  read_feeBase sevm 1 _ s

theorem stop_projections (B : Devm) (S : List B256) (M' : Mem) (G' : Nat) (a : Adr) :
    (St B S M' G').getStor a = B.getStor a ∧ (St B S M' G').getBal a = B.getBal a ∧
      (St B S M' G').logs = B.logs ∧ (St B S M' G').output = B.output :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem addLog_getBal (w : Devm) (l : Log) (a : Adr) :
    (w.addLog l).getBal a = w.getBal a := rfl

theorem addLog_output (w : Devm) (l : Log) : (w.addLog l).output = w.output := rfl

theorem afterSload_getBal (sevm : Sevm) (w : Devm) (k : B256) (a : Adr) :
    (afterSload sevm w k).getBal a = w.getBal a := by
  simp only [Devm.getBal, afterSload_getAcct]

end Tail

namespace UserPath

variable {k : UserPath} {sevm : Sevm} {pre post : Devm}

/-- **The fork of a user frame.** A successful execution at a non-system caller from an empty stack passes
the guard, quotes the fee, and either reaches the submission arm at the submission's length, or is a fee read
on empty calldata. `lengthBound` holds of any calldata a frame can carry, since `CALLDATASIZE` is read as a
word. -/
theorem exec_user_cases (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    (pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧ sevm.data.length = k.shape.len.word.toNat ∧
      ∃ iterations finalOutput,
        WordFakeExponential.Run (storedExcess k.shape.target.word sevm pre) 17 1 17 0 iterations
          finalOutput ∧
        ∃ G0, SFunc.Run k.cert.prog sevm (St (feeBase sevm pre) [finalOutput / (17 : B256)] pre.memory G0)
          k.submission (.halted post)) ∨
    (sevm.data = [] ∧ ∃ iterations finalOutput, FeeRead k.target sevm pre post iterations finalOutput) := by
  obtain ⟨_, run⟩ := exec_user hcode fork stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, G0, run⟩ :=
    feePath_inv k.shape fork k.revert_noOk k.window k.loop run
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
    exact ⟨literal, exec_fee_read hcode fork stack aligned wf caller literal exec⟩

end UserPath

/-- At excess 0 the fee recurrence takes one step and quotes 1 wei. -/
theorem quote_zero_excess : WordFakeExponential.Run 0 17 1 17 0 1 17 := by
  have next : WordFakeExponential.nextAccumulator 0 17 1 17 = 0 := by decide
  have sum : (0 : B256) + 17 = 17 := by decide
  refine .step (by decide) ?_
  rw [next, sum]
  exact .stop _ _

end Blanc.Lift.BuilderRequest
