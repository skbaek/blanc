import Blanc.Lift.RequestFee.Getter
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.PackedSha
import Blanc.Lift.ExactWalkSolc
import Blanc.RequestFeeWord
import Blanc.Lift.RequestSystem.Dispatch

/-!
# The EIP-8282 builder contracts' user fee path

Both builder runtimes share one user path up to the calldata-length branch: caller dispatch, the
slot-zero inhibitor guard, the read of the excess adjusted by the count over target
(`targetExcess`), and the shared fee window. Only the pushed target and jump targets, the calldata
length and the continuation trees differ, so a generated tree is an instance of `feePathTree` by
`rfl`.

These are statements about the code's walk, over any storage. Nothing here says which storage is
reachable. Every walk here, both directions, is over a fork's `StorageSteps`: the only steps of these
contracts' frames that differ between covered forks and Amsterdam are `SLOAD` and `SSTORE`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestFee (PushWord feeLoopGas initTree loopTree postloopTree selected)
open RequestSystem (dispatchTree dispatchArm dispatchGas dispatch_exact system_push)

/-- The excess the builder codes quote the fee from, read off the bytes: `slot0 + (count - target)`
in words when `count > target`, else `slot0`. See `targetExcess_toNat` for its natural value. -/
def targetExcess (target slot0 count : B256) : B256 :=
  if target < count then (count - target) + slot0 else slot0

/-- The quoted excess is `slot0 + max(0, count - target)`, reduced modulo the word. -/
theorem targetExcess_toNat (target slot0 count : B256) :
    (targetExcess target slot0 count).toNat =
      (slot0.toNat + (count.toNat - target.toNat)) % 2 ^ 256 := by
  unfold targetExcess
  by_cases over : target < count
  · have lt := B256.lt_iff_toNat_lt_toNat.mp over
    have sub : (count - target).toNat = count.toNat - target.toNat := by
      rw [B256.toNat_sub, Nat.lo, Nat.add_sub_mod_eq_sub (B256.toNat_lt count) (Nat.le_of_lt lt)]
    rw [ite_eq_left over, B256.toNat_add, sub, Nat.add_comm]
    rfl
  · have le : count.toNat ≤ target.toNat :=
      Nat.le_of_not_lt (fun lt => over (B256.lt_iff_toNat_lt_toNat.mpr lt))
    rw [ite_eq_right over, Nat.sub_eq_zero_of_le le, Nat.add_zero,
      Nat.mod_eq_of_lt (B256.toNat_lt slot0)]

/-- The fixed charge of `feePathTree` up to the selected continuation, excluding the two `SLOAD`s
and the fee loop. The two arms of the count test cost the same. -/
def feePathFixedGas : Nat := 133

/-- A fork's storage steps as a frame's walk sees them: the successor bases of `SLOAD` and `SSTORE`, what a
store takes from `gasLeft`, and what it returns there. Everything else in these frames is fork-free. -/
structure StorageSteps (sevm : Sevm) where
  /-- The base after a read of a key. -/
  afterRead : Devm → B256 → Devm
  /-- The base after a write of a key. -/
  afterWrite : Devm → B256 → B256 → Devm
  /-- What a write takes from `gasLeft`. -/
  writeCharge : Devm → B256 → B256 → Nat
  /-- What a write returns to `gasLeft`, after its charge. -/
  writeRepay : Devm → B256 → B256 → Nat

/-- That the fork's steps are what its rules execute, both ways. -/
structure StorageSteps.Valid {sevm : Sevm} (l : StorageSteps sevm) : Prop where
  push0 : sevm.benvStat.rules.op.push0 = true
  shifts : sevm.benvStat.rules.op.shifts = true
  readRun : ∀ {fs : List SFunc} {f : SFunc} {o : Outcome} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {k : B256}, S.length < 1024 →
    SFunc.RunExact fs sevm (St (l.afterRead b k) (b.getStorVal sevm.currentTarget k :: S) M G) f o →
    SFunc.RunExact fs sevm (St b (k :: S) M (G + sloadCost sevm b k)) (.next (.reg .sload) f) o
  readInv : ∀ {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {k : B256},
    Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d →
    ∃ G', d = St (l.afterRead b k) (b.getStorVal sevm.currentTarget k :: S) M G'
  writeRun : ∀ {fs : List SFunc} {f : SFunc} {o : Outcome} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {k x : B256}, sevm.isStatic = false → gCallStipend < G + l.writeCharge b k x →
    SFunc.RunExact fs sevm (St (l.afterWrite b k x) S M (G + l.writeRepay b k x)) f o →
    SFunc.RunExact fs sevm (St b (k :: x :: S) M (G + l.writeCharge b k x)) (.next (.reg .sstore) f) o
  writeInv : ∀ {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {k x : B256},
    Ninst.Run sevm (St b (k :: x :: S) M G) (.reg .sstore) d →
    ∃ G', d = St (l.afterWrite b k x) S M G'
  writeDynamic : ∀ {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {k x : B256},
    Ninst.Run sevm (St b (k :: x :: S) M G) (.reg .sstore) d → sevm.isStatic = false
  readState : ∀ b k, (l.afterRead b k).state = b.state
  readLogs : ∀ b k, (l.afterRead b k).logs = b.logs
  readOutput : ∀ b k, (l.afterRead b k).output = b.output
  writeState : ∀ b k x, (l.afterWrite b k x).state = b.state.setStorVal sevm.currentTarget k x
  writeLogs : ∀ b k x, (l.afterWrite b k x).logs = b.logs
  writeOutput : ∀ b k x, (l.afterWrite b k x).output = b.output

/-- The covered forks' storage steps: no state gas, so nothing is repaid. -/
def coveredSteps (sevm : Sevm) : StorageSteps sevm where
  afterRead := afterSload sevm
  afterWrite := afterSstore sevm
  writeCharge := sstoreCost sevm
  writeRepay := fun _ _ _ => 0

/-- The covered forks' steps are what those forks execute. -/
theorem coveredSteps_valid {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork) :
    (coveredSteps sevm).Valid where
  push0 := fork.rules_push0
  shifts := fork.rules_shifts
  readRun := fun hroom k => rx_sload_sel fork hroom k
  readInv := fun h => ri_sload fork h
  writeRun := fun dynamic slack k => rx_sstore fork slack dynamic k
  writeInv := fun h => ri_sstore fork h
  writeDynamic := fun h => ri_sstore_nonstatic fork h
  readState := fun b k => by
    show (afterSload sevm b k).state = b.state
    unfold afterSload
    split <;> rfl
  readLogs := fun _ _ => afterSload_logs sevm _ _
  readOutput := fun _ _ => afterSload_output sevm _ _
  writeState := fun b k x => by
    show (afterSstore sevm b k x).state = _
    unfold afterSstore
    split <;> rfl
  writeLogs := fun _ _ _ => afterSstore_logs sevm _ _ _
  writeOutput := fun _ _ _ => afterSstore_output sevm _ _ _

namespace StorageSteps

variable {sevm : Sevm} (l : StorageSteps sevm)

/-- The fee path's base after its two reads: slots 0 and 1 warmed. -/
def feeBase (b : Devm) : Devm := l.afterRead (l.afterRead b 0) 1

/-- The exact charge of `feePathTree`. -/
def feePathGas (b : Devm) (iterations : Nat) : Nat :=
  feePathFixedGas + RequestFee.feeLoopGas iterations + sloadCost sevm b 0 + sloadCost sevm (l.afterRead b 0) 1

variable {l}

theorem Valid.getStorVal_read (v : l.Valid) (b : Devm) (k : B256) (a : Adr) (k' : B256) :
    (l.afterRead b k).getStorVal a k' = b.getStorVal a k' := by
  unfold Devm.getStorVal Devm.getAcct
  rw [v.readState]

theorem Valid.getStor_feeBase (v : l.Valid) (b : Devm) (a : Adr) :
    (l.feeBase b).getStor a = b.getStor a := by
  show ((l.feeBase b).state.get a).stor = (b.state.get a).stor
  rw [feeBase, v.readState, v.readState]

theorem Valid.getBal_feeBase (v : l.Valid) (b : Devm) (a : Adr) :
    (l.feeBase b).getBal a = b.getBal a := by
  show ((l.feeBase b).state.get a).bal = (b.state.get a).bal
  rw [feeBase, v.readState, v.readState]

theorem Valid.logs_feeBase (v : l.Valid) (b : Devm) : (l.feeBase b).logs = b.logs := by
  rw [feeBase, v.readLogs, v.readLogs]

/-- A store's repayment, named: it then sinks below the walk's remaining charges with
`Nat.add_right_comm`. -/
theorem Valid.write_sink {fs : List SFunc} {f : SFunc} {o : Outcome} {b : Devm} {S : List B256} {M : Mem}
    {X : Nat} {k x : B256} (v : l.Valid) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < X + l.writeCharge b k x)
    (next : ∀ r, r = l.writeRepay b k x → SFunc.RunExact fs sevm (St (l.afterWrite b k x) S M (X + r)) f o) :
    SFunc.RunExact fs sevm (St b (k :: x :: S) M (X + l.writeCharge b k x)) (.next (.reg .sstore) f) o :=
  v.writeRun dynamic slack (next _ rfl)

end StorageSteps

/-- The storage reads of the fee path leave the frame's state with slots 0 and 1 warmed. -/
def feeBase (sevm : Sevm) (b : Devm) : Devm := (coveredSteps sevm).feeBase b

/-- `slot0 + max(0, count - target)` from the frame's own storage. -/
def storedExcess (target : B256) (sevm : Sevm) (b : Devm) : B256 :=
  targetExcess target (b.getStorVal sevm.currentTarget 0) (b.getStorVal sevm.currentTarget 1)

/-- `PUSH0; SLOAD; DUP1; PUSH32 MAX; EQ; PUSH dest; JUMPI`: revert when slot 0 is the inhibitor. -/
def inhibitorTree (dest : PushWord) (active revert : SFunc) : SFunc :=
  (.next (.push [] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
  (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff] (by decide)) (.next (.reg .eq)
  (.next (.push (dest.head :: dest.tail) dest.le) (.branch active revert)))))))

/-- Read the count; add `count - target` to the excess only when `count > target`. -/
def excessTree (target over under : PushWord) (window : Nat) (fall : SFunc) : SFunc :=
  (.next (.push [0x01] (by decide)) (.next (.reg .sload)
  (.next (.push (target.head :: target.tail) target.le) (.next (.reg (.dup 1)) (.next (.reg .gt)
  (.next (.push (over.head :: over.tail) over.le)
  (.branch
    (.next (.reg .pop) (.next (.push (under.head :: under.tail) under.le) (.jump window)))
    (.dest (.next (.push (target.head :: target.tail) target.le) (.next (.reg (.swap 0))
      (.next (.reg .sub) (.next (.reg .add) fall))))))))))))

/-- `JUMPDEST; PUSH1 17; SWAP1`, then the shared setup. -/
def windowTree (header : SFunc) : SFunc :=
  (.dest (.next (.push [0x11] (by decide)) (.next (.reg (.swap 0)) (initTree header))))

/-- The pushed words and program entries a builder contract's fee path differs by. -/
structure Shape where
  /-- Destination of the inhibitor's revert. -/
  revert : PushWord
  /-- The per-block target. -/
  target : PushWord
  /-- Destination taken when `count > target`. -/
  over : PushWord
  /-- Destination taken otherwise. -/
  under : PushWord
  /-- Program entry of the window. -/
  window : Nat
  /-- Destination leaving the fee loop. -/
  post : PushWord
  /-- Destination of the fee loop's backedge. -/
  loop : PushWord
  /-- Program entry of the fee loop. -/
  loopEntry : Nat
  /-- The submission's calldata length. -/
  len : PushWord
  /-- Destination taken at that length. -/
  submit : PushWord

variable (p : Shape)

/-- The window with its loop and postloop. -/
def windowOf (getter submission : SFunc) : SFunc :=
  windowTree (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission))

/-- The user path from the inhibitor guard to the calldata-length branch. -/
def feePathTree (revert getter submission : SFunc) : SFunc :=
  inhibitorTree p.revert
    (excessTree p.target p.over p.under p.window (windowOf p getter submission)) revert

variable {fs : List SFunc} {sevm : Sevm} {l : StorageSteps sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- A successful dispatch reaches the arm the caller selects, on the same stack and memory. -/
theorem dispatch_inv {dest : PushWord} {user system : SFunc}
    (run : SFunc.Run fs sevm (St b [] M G) (dispatchTree dest user system) o) :
    ∃ G', SFunc.Run fs sevm (St b [] M G') (dispatchArm sevm user system) o := by
  have run := run.cut
  unfold dispatchTree at run
  winv 2
  rw [system_push] at run
  winv 1
  rw [adr_eqCheck] at run
  winv 1
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨flag, G', run⟩
  · have hcaller : sevm.caller ≠ systemAddress := by
      intro hc
      rw [ite_eq_left hc] at flag
      exact (by decide : (1 : B256) ≠ 0) flag
    exact ⟨G', by simpa only [dispatchArm, ite_eq_right hcaller] using run.uncut⟩
  · have hcaller : sevm.caller = systemAddress := by
      by_contra hc
      rw [ite_eq_right hc] at flag
      exact flag rfl
    exact ⟨G', by simpa only [dispatchArm, ite_eq_left hcaller] using run.uncut⟩

/-- A run past the guard has slot 0 off the inhibitor. -/
theorem inhibitor_inv {dest : PushWord} {active revert : SFunc}
    (v : l.Valid) (noOk : revert.noOk = true)
    (run : SFunc.Run fs sevm (St b [] M G) (inhibitorTree dest active revert) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
      ∃ G', SFunc.Run fs sevm
        (St (l.afterRead b 0) [b.getStorVal sevm.currentTarget 0] M G') active o := by
  have run := run.cut
  unfold inhibitorTree at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.readInv (k := (0 : B256)) h
  winv 2
  rw [inhibitor_push] at run
  winv 2
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨_, _, run⟩
  · refine ⟨?_, G', run.uncut⟩
    intro inhibited
    simp only [inhibited, B256.eqCheck, ite_true] at flag
    exact (by decide : (1 : B256) ≠ 0) flag
  · exact False.elim (run.false_of_noOk noOk)

/-- The guard, forward, off the inhibitor. -/
theorem inhibitor_exact (v : l.Valid) {dest : PushWord} {active revert : SFunc}
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (tail : SFunc.RunExact fs sevm
      (St (l.afterRead b 0) [b.getStorVal sevm.currentTarget 0] M G) active o) :
    SFunc.RunExact fs sevm (St b [] M (G + 22 + sloadCost sevm b 0 + 2))
      (inhibitorTree dest active revert) o := by
  have hgas : G + 22 + sloadCost sevm b 0 + 2 =
      G + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 := by
    omega
  rw [hgas]
  unfold inhibitorTree
  refine rx_push0 (h_push0 := v.push0) (by change 0 < 1024; decide) ?_
  refine v.readRun (by change 0 < 1024; decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push inhibitor_push (by change 2 < 1024; decide) ?_
  refine rx_eq (v := 0) ?_ (by change 1 < 1024; decide) ?_
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm off)]
  · refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact rx_branch_zero tail

/-- The excess read leaves the target-adjusted excess at the window. -/
theorem excess_inv {target over under : PushWord} {window : Nat} {fall : SFunc}
    (v : l.Valid) (entry : fs[window]? = some fall)
    {slot0 : B256}
    (run : SFunc.Run fs sevm (St b [slot0] M G) (excessTree target over under window fall) o) :
    ∃ G', SFunc.Run fs sevm
      (St (l.afterRead b 1)
        [targetExcess target.word slot0 (b.getStorVal sevm.currentTarget 1)] M G') fall o := by
  have run := run.cut
  unfold excessTree at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.readInv (k := (1 : B256)) h
  generalize hcount' : b.getStorVal sevm.currentTarget 1 = count at run
  winv 4
  rcases ric_branch run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · have notOver : ¬ target.word < count := by
      intro lt
      simp only [B256.gtCheck, ite_eq_left lt] at flag
      exact (by decide : (1 : B256) ≠ 0) flag
    winv 2
    obtain ⟨G', run⟩ := ric_jump (by intro h; cases h) entry run
    refine ⟨G', ?_⟩
    simpa only [targetExcess, ite_eq_right notOver] using run.uncut
  · have isOver : target.word < count := by
      by_contra notLt
      simp only [B256.gtCheck, ite_eq_right notLt] at flag
      exact flag rfl
    winv 5
    have excess : targetExcess target.word slot0 count = count - target.word + slot0 := by
      simp only [targetExcess, ite_eq_left isOver]
    rw [excess]
    exact ⟨_, run.uncut⟩

/-- The excess read, forward, at its exact charge. -/
theorem excess_exact (v : l.Valid) {target over under : PushWord} {window : Nat}
    {fall : SFunc} (entry : fs[window]? = some fall) {slot0 : B256}
    (tail : SFunc.RunExact fs sevm
      (St (l.afterRead b 1)
        [targetExcess target.word slot0 (b.getStorVal sevm.currentTarget 1)] M G) fall o) :
    SFunc.RunExact fs sevm (St b [slot0] M (G + 35 + sloadCost sevm b 1 + 3))
      (excessTree target over under window fall) o := by
  have hgas : G + 35 + sloadCost sevm b 1 + 3 =
      G + 13 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 1 + 3 := by
    omega
  rw [hgas]
  unfold excessTree
  refine rx_push (w := (1 : B256)) rfl (by change 1 < 1024; decide) ?_
  refine v.readRun (by change 1 < 1024; decide) ?_
  generalize hcount : b.getStorVal sevm.currentTarget 1 = count at tail ⊢
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_gt rfl (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  by_cases isOver : target.word < count
  · have flag : B256.gtCheck count target.word = 1 := by
      simp only [B256.gtCheck, ite_eq_left isOver]
    rw [flag]
    refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
    have tail' : SFunc.RunExact fs sevm
        (St (l.afterRead b 1) [(count - target.word) + slot0] M G) fall o := by
      simpa only [targetExcess, ite_eq_left isOver] using tail
    have hgas' : G + 13 = G + 3 + 3 + 3 + 3 + 1 := by simp only [Nat.add_assoc]
    rw [hgas']
    refine rx_dest ?_
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_swap1 ?_
    refine rx_sub' rfl (by change 1 < 1024; decide) ?_
    exact rx_add' rfl (by decide) tail'
  · have flag : B256.gtCheck count target.word = 0 := by
      simp only [B256.gtCheck, ite_eq_right isOver]
    rw [flag]
    refine rx_branch_zero ?_
    have tail' : SFunc.RunExact fs sevm (St (l.afterRead b 1) [slot0] M G) fall o := by
      simpa only [targetExcess, ite_eq_right isOver] using tail
    have hgas' : G + 13 = G + 8 + 3 + 2 := by simp only [Nat.add_assoc]
    rw [hgas']
    refine rx_pop ?_
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_jump entry tail'

/-- A successful run of the user path passes the guard, runs the word fee recurrence on the stored
excess, and reaches the branch the calldata length selects with the quotient on the stack. -/
theorem feePath_inv {revert getter submission : SFunc}
    (v : l.Valid) (noOk : revert.noOk = true)
    (window : fs[p.window]? = some (windowOf p getter submission))
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (run : SFunc.Run fs sevm (St b [] M G) (feePathTree p revert getter submission) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (storedExcess p.target.word sevm b) 17 1 17 0 iterations finalOutput ∧
      ∃ G', SFunc.Run fs sevm (St (l.feeBase b) [finalOutput / (17 : B256)] M G')
        (selected sevm p.len.word getter submission) o := by
  obtain ⟨active, _, run⟩ := inhibitor_inv v noOk run
  obtain ⟨_, run⟩ := excess_inv v window run
  have read0 : (l.afterRead b 0).getStorVal sevm.currentTarget 1 =
      b.getStorVal sevm.currentTarget 1 := v.getStorVal_read b 0 _ 1
  rw [read0] at run
  obtain ⟨iterations, finalOutput, wordRun, _⟩ :=
    WordFakeExponential.run_exists (storedExcess p.target.word sevm b) 17 1 17 0
  refine ⟨active, iterations, finalOutput, wordRun, ?_⟩
  have run := run.cut
  winv 3
  obtain ⟨_, run⟩ := RequestFee.init_inv run.uncut
  obtain ⟨_, _, run⟩ := RequestFee.loop_inv loop wordRun run
  exact RequestFee.postloop_inv rfl run

/-- The user path, forward: the selected continuation transports back at the exact charge. -/
theorem feePath_exact (v : l.Valid) {revert getter submission : SFunc}
    {iterations : Nat} {finalOutput : B256}
    (window : fs[p.window]? = some (windowOf p getter submission))
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess p.target.word sevm b) 17 1 17 0
      iterations finalOutput)
    (tail : SFunc.RunExact fs sevm (St (l.feeBase b) [finalOutput / (17 : B256)] M G)
      (selected sevm p.len.word getter submission) o) :
    SFunc.RunExact fs sevm (St b [] M (G + l.feePathGas b iterations))
      (feePathTree p revert getter submission) o := by
  have read0 : (l.afterRead b 0).getStorVal sevm.currentTarget 1 =
      b.getStorVal sevm.currentTarget 1 := v.getStorVal_read b 0 _ 1
  have hloop := fun finalCounter => (RequestFee.postloop_exact (len := p.len) (dest := p.submit)
    (w := p.len.word) (numerator := storedExcess p.target.word sevm b) (denominator := 17)
    (accumulator := 0) (output := finalOutput) (counter := finalCounter) (fs := fs) rfl
    (getter := getter) (submission := submission) tail)
  have hlooped := RequestFee.loop_exact loop v.push0 wordRun hloop
  have hinit := RequestFee.init_exact v.push0 hlooped
  have hwindow : SFunc.RunExact fs sevm
      (St (l.feeBase b) [storedExcess p.target.word sevm b] M
        (G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1)) (windowOf p getter submission) o := by
    unfold windowOf windowTree
    refine rx_dest ?_
    refine rx_push (w := (17 : B256)) rfl (by change 1 < 1024; decide) ?_
    refine rx_swap1 ?_
    exact hinit
  have hexcess := excess_exact v (b := l.afterRead b 0) (target := p.target) (over := p.over)
    (under := p.under) (slot0 := b.getStorVal sevm.currentTarget 0) window (by
      rw [read0]
      exact hwindow)
  have hguard := inhibitor_exact v (dest := p.revert) (revert := revert) off hexcess
  have hgas : G + l.feePathGas b iterations =
      G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1 + 35 + sloadCost sevm (l.afterRead b 0) 1 + 3
        + 22 + sloadCost sevm b 0 + 2 := by
    simp only [StorageSteps.feePathGas, feePathFixedGas]
    omega
  rw [hgas]
  exact hguard

/-- A builder runtime's user path: a checked certificate whose root is caller dispatch into
`feePathTree`, whose empty-calldata arm is the shared getter. -/
structure UserPath where
  /-- The runtime bytes. -/
  code : ByteArray
  /-- Its certificate. -/
  cert : Cert
  check : Cert.check code cert = true
  jumps : Cert.jumpsOk code cert = true
  /-- No node of the certificate is a call-family instruction, so the lift holds on any fork. -/
  noExec : ProgNoExec cert.prog
  /-- The pushed words of the fee path. -/
  shape : Shape
  /-- Destination of the system arm. -/
  systemDest : PushWord
  /-- The system arm. -/
  system : SFunc
  /-- The inhibitor's revert arm. -/
  revert : SFunc
  /-- Destination of the getter's revert. -/
  getterDest : PushWord
  /-- The getter's revert arm. -/
  getterRevert : SFunc
  /-- The arm at the submission's calldata length. -/
  submission : SFunc
  root : cert.prog[0]? = some (dispatchTree systemDest
    (feePathTree shape revert (RequestFee.guardTree getterDest RequestFee.returnTree getterRevert)
      submission) system)
  window : cert.prog[shape.window]? = some (windowOf shape
    (RequestFee.guardTree getterDest RequestFee.returnTree getterRevert) submission)
  loop : cert.prog[shape.loopEntry]? = some (loopTree shape.post shape.loop shape.loopEntry
    (postloopTree shape.len shape.submit
      (RequestFee.guardTree getterDest RequestFee.returnTree getterRevert) submission))
  revert_noOk : revert.noOk = true
  getterRevert_noOk : getterRevert.noOk = true
  len_ne : shape.len.word ≠ 0

namespace UserPath

variable (k : UserPath)

/-- The getter arm. -/
abbrev getter : SFunc := RequestFee.guardTree k.getterDest RequestFee.returnTree k.getterRevert

/-- The user arm of caller dispatch. -/
abbrev user : SFunc := feePathTree k.shape k.revert k.getter k.submission

/-- The per-block target as a word. -/
abbrev target : B256 := k.shape.target.word

variable {k} {pre post : Devm}

/-- Successful execution from an empty stack at a non-system caller enters the fee path. The lift holds on
any fork, since the certificate has no call-family node. -/
theorem exec_user (hcode : sevm.code = k.code) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    ∃ G, SFunc.Run k.cert.prog sevm (St pre [] pre.memory G) k.user (.halted post) := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec k.check hcode k.noExec exec
  rw [k.root] at hf
  cases hf
  rw [St.self stack rfl] at run
  obtain ⟨G, run⟩ := dispatch_inv run
  exact ⟨G, by simpa only [dispatchArm, ite_eq_right caller] using run⟩

/-- An exact fee path at a non-system caller is a successful execution of the bytes. -/
theorem exec_of_user (hcode : sevm.code = k.code) (caller : sevm.caller ≠ systemAddress)
    (tail : SFunc.RunExact k.cert.prog sevm (St b [] M G) k.user (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) := by
  apply lift_exact_noExec k.check k.jumps hcode k.noExec
  refine ⟨_, k.root, dispatch_exact ?_⟩
  simpa only [dispatchArm, ite_eq_right caller] using tail

/-- While slot 0 holds the inhibitor, no execution at a non-system caller succeeds, whatever the
calldata, value and memory. -/
theorem exec_inhibited_no_ok (v : l.Valid) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  exact (inhibitor_inv v k.revert_noOk run).1 inhibited

/-- What a successful fee read does on a fork's steps, for the fee recurrence's iteration count and final
output. `FeeRead` is this under covered forks. -/
structure FeeReadOn (l : StorageSteps sevm) (target : B256) (pre post : Devm) (iterations : Nat)
    (finalOutput : B256) : Prop where
  /-- The read carried no value. -/
  value : sevm.value = 0
  /-- Slot 0 is not the inhibitor. -/
  active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The word recurrence ran on `slot0 + max(0, count - target)`. -/
  quote : WordFakeExponential.Run (storedExcess target sevm pre) 17 1 17 0 iterations finalOutput
  /-- The return bytes are the quotient, as one word. -/
  output : post.output = (finalOutput / (17 : B256)).toBytes
  /-- No account's storage changed. -/
  storage : ∀ address, post.getStor address = pre.getStor address
  /-- No balance changed. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- No log was appended. -/
  logs : post.logs = pre.logs
  /-- The whole post state: storage keys warmed, the word in memory, the rest unchanged. -/
  state : ∃ gas, post = RequestFee.feeGetterPost (l.feeBase pre) pre.memory
    (finalOutput / (17 : B256)) gas

/-- What a successful fee read does under covered forks. -/
abbrev FeeRead (target : B256) (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop :=
  FeeReadOn (coveredSteps sevm) target pre post iterations finalOutput

/-- The quoted word fee is at most `fake_exponential(1, excess, 17)` of the quoted excess. -/
theorem FeeReadOn.fee_le {target : B256} {iterations : Nat} {finalOutput : B256}
    (read : FeeReadOn l target pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat ≤ fakeExp 1 (storedExcess target sevm pre).toNat 17 :=
  RequestFeeWord.word_fee_le read.quote

/-- The quoted word fee equals the natural fee exactly on the recurrence's no-wrap domain. -/
theorem FeeReadOn.fee_eq_iff {target : B256} {iterations : Nat} {finalOutput : B256}
    (read : FeeReadOn l target pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 (storedExcess target sevm pre).toNat 17 ↔
      RequestFeeWord.NoWrapDomain (storedExcess target sevm pre) iterations :=
  RequestFeeWord.word_fee_eq_iff read.quote

/-- A successful empty-calldata execution at a non-system caller is a fee read. -/
theorem exec_fee_read (v : l.Valid) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, FeeReadOn l k.target pre post iterations finalOutput := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, _, run⟩ :=
    feePath_inv k.shape v k.revert_noOk k.window k.loop run
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  simp only [selected, ite_eq_right hlen] at run
  obtain ⟨_, zero, _, run⟩ := RequestFee.guard_inv k.getterRevert_noOk run
  obtain ⟨gas, rfl⟩ := RequestFee.return_inv aligned run
  have facts := RequestFee.feeGetterPost_facts (l.feeBase pre) pre.memory
    (finalOutput / (17 : B256)) gas wf aligned
  refine ⟨iterations, finalOutput, zero, active, wordRun, facts.1, ?_, ?_, ?_, gas, rfl⟩
  · intro address
    rw [← v.getStor_feeBase pre address]
    exact congrArg (fun world : World => (world.state.get address).stor) facts.2.1
  · intro address
    rw [← v.getBal_feeBase pre address]
    exact congrArg (fun world : World => (world.state.get address).bal) facts.2.1
  · rw [← v.logs_feeBase pre]
    exact (congrArg Meta.logs facts.2.2.1).trans rfl

/-- The charge of a fee read, from the frame's start, on a fork's steps. -/
def feeReadGasOn (l : StorageSteps sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  RequestFee.feeGetterGas M + 30 + l.feePathGas b iterations + dispatchGas

/-- The charge of a fee read, from the frame's start, under covered forks. -/
def feeReadGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  feeReadGasOn (coveredSteps sevm) b M iterations

/-- The fee read forward: empty calldata, no value and slot 0 off the inhibitor give a successful
execution at the exact charge, returning the word recurrence's quotient. The recurrence always has
a finite run (`WordFakeExponential.run_exists`), so this premise can always be met. -/
theorem exec_fee_read_exact {iterations : Nat} {finalOutput : B256} (v : l.Valid)
    (hcode : sevm.code = k.code) (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target sevm b) 17 1 17 0
      iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + feeReadGasOn l b M iterations))
      (.ok (RequestFee.feeGetterPost (l.feeBase b) M (finalOutput / (17 : B256)) G))) := by
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  have hempty : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have body := RequestFee.guard_exact (dest := k.getterDest) (revert := k.getterRevert)
    (fs := k.cert.prog) hempty zero
    (RequestFee.return_exact (b := l.feeBase b) (M := M) (G := G)
      (fee := finalOutput / (17 : B256)) v.push0 aligned)
  have path := feePath_exact k.shape v (revert := k.revert) (submission := k.submission)
    k.window k.loop off wordRun
    (by simpa only [selected, ite_eq_right hlen] using body)
  have hgas : G + feeReadGasOn l b M iterations =
      (G + RequestFee.feeGetterGas M + 30 + l.feePathGas b iterations) + dispatchGas := by
    simp only [feeReadGasOn, Nat.add_assoc]
  rw [hgas]
  exact exec_of_user hcode caller path

/-- The fee read forward, with what it does: returns the quotient, and changes no storage, balance or log. -/
theorem exec_fee_read_effects {iterations : Nat} {finalOutput : B256} (v : l.Valid)
    (hcode : sevm.code = k.code) (aligned : M.size % 32 = 0) (wf : Mem.Wf M)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target sevm b) 17 1 17 0
      iterations finalOutput) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] M (G + feeReadGasOn l b M iterations)) (.ok post)) ∧
      post.output = (finalOutput / (17 : B256)).toBytes ∧
      (∀ a, post.getStor a = b.getStor a) ∧ (∀ a, post.getBal a = b.getBal a) ∧ post.logs = b.logs := by
  have facts := RequestFee.feeGetterPost_facts (l.feeBase b) M (finalOutput / (17 : B256)) G wf aligned
  refine ⟨_, exec_fee_read_exact v hcode aligned caller empty zero off wordRun, facts.1, ?_, ?_, ?_⟩
  · intro address
    rw [← v.getStor_feeBase b address]
    exact congrArg (fun world : World => (world.state.get address).stor) facts.2.1
  · intro address
    rw [← v.getBal_feeBase b address]
    exact congrArg (fun world : World => (world.state.get address).bal) facts.2.1
  · rw [← v.logs_feeBase b]
    exact (congrArg Meta.logs facts.2.2.1).trans rfl

end UserPath

end Blanc.Lift.BuilderRequest
