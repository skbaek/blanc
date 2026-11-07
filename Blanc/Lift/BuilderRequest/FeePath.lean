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
reachable, and nothing here is stated for Amsterdam.
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

/-- The storage reads of the fee path leave the frame's state with slots 0 and 1 warmed. -/
def feeBase (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (afterSload sevm b 0) 1

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

/-- The fixed charge of `feePathTree` up to the selected continuation, excluding the two `SLOAD`s
and the fee loop. The two arms of the count test cost the same. -/
def feePathFixedGas : Nat := 133

/-- The exact charge of `feePathTree`. -/
def feePathGas (sevm : Sevm) (b : Devm) (iterations : Nat) : Nat :=
  feePathFixedGas + feeLoopGas iterations + sloadCost sevm b 0 +
    sloadCost sevm (afterSload sevm b 0) 1

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

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
    (fork : CoveredFork sevm.benvStat.fork) (noOk : revert.noOk = true)
    (run : SFunc.Run fs sevm (St b [] M G) (inhibitorTree dest active revert) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
      ∃ G', SFunc.Run fs sevm
        (St (afterSload sevm b 0) [b.getStorVal sevm.currentTarget 0] M G') active o := by
  have run := run.cut
  unfold inhibitorTree at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork (k := (0 : B256)) h
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
theorem inhibitor_exact {dest : PushWord} {active revert : SFunc}
    (fork : CoveredFork sevm.benvStat.fork)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (tail : SFunc.RunExact fs sevm
      (St (afterSload sevm b 0) [b.getStorVal sevm.currentTarget 0] M G) active o) :
    SFunc.RunExact fs sevm (St b [] M (G + 22 + sloadCost sevm b 0 + 2))
      (inhibitorTree dest active revert) o := by
  have hgas : G + 22 + sloadCost sevm b 0 + 2 =
      G + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 := by
    omega
  rw [hgas]
  unfold inhibitorTree
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 0 < 1024; decide) ?_
  refine rx_sload_sel fork (by change 0 < 1024; decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push inhibitor_push (by change 2 < 1024; decide) ?_
  refine rx_eq (v := 0) ?_ (by change 1 < 1024; decide) ?_
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm off)]
  · refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact rx_branch_zero tail

/-- The excess read leaves the target-adjusted excess at the window. -/
theorem excess_inv {target over under : PushWord} {window : Nat} {fall : SFunc}
    (fork : CoveredFork sevm.benvStat.fork) (entry : fs[window]? = some fall)
    {slot0 : B256}
    (run : SFunc.Run fs sevm (St b [slot0] M G) (excessTree target over under window fall) o) :
    ∃ G', SFunc.Run fs sevm
      (St (afterSload sevm b 1)
        [targetExcess target.word slot0 (b.getStorVal sevm.currentTarget 1)] M G') fall o := by
  have run := run.cut
  unfold excessTree at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork (k := (1 : B256)) h
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
theorem excess_exact {target over under : PushWord} {window : Nat} {fall : SFunc}
    (fork : CoveredFork sevm.benvStat.fork) (entry : fs[window]? = some fall)
    {slot0 : B256}
    (tail : SFunc.RunExact fs sevm
      (St (afterSload sevm b 1)
        [targetExcess target.word slot0 (b.getStorVal sevm.currentTarget 1)] M G) fall o) :
    SFunc.RunExact fs sevm (St b [slot0] M (G + 35 + sloadCost sevm b 1 + 3))
      (excessTree target over under window fall) o := by
  have hgas : G + 35 + sloadCost sevm b 1 + 3 =
      G + 13 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 1 + 3 := by
    omega
  rw [hgas]
  unfold excessTree
  refine rx_push (w := (1 : B256)) rfl (by change 1 < 1024; decide) ?_
  refine rx_sload_sel fork (by change 1 < 1024; decide) ?_
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
        (St (afterSload sevm b 1) [(count - target.word) + slot0] M G) fall o := by
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
    have tail' : SFunc.RunExact fs sevm (St (afterSload sevm b 1) [slot0] M G) fall o := by
      simpa only [targetExcess, ite_eq_right isOver] using tail
    have hgas' : G + 13 = G + 8 + 3 + 2 := by simp only [Nat.add_assoc]
    rw [hgas']
    refine rx_pop ?_
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_jump entry tail'

/-- A successful run of the user path passes the guard, runs the word fee recurrence on the stored
excess, and reaches the branch the calldata length selects with the quotient on the stack. -/
theorem feePath_inv {revert getter submission : SFunc}
    (fork : CoveredFork sevm.benvStat.fork) (noOk : revert.noOk = true)
    (window : fs[p.window]? = some (windowOf p getter submission))
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (run : SFunc.Run fs sevm (St b [] M G) (feePathTree p revert getter submission) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (storedExcess p.target.word sevm b) 17 1 17 0 iterations finalOutput ∧
      ∃ G', SFunc.Run fs sevm (St (feeBase sevm b) [finalOutput / (17 : B256)] M G')
        (selected sevm p.len.word getter submission) o := by
  obtain ⟨active, _, run⟩ := inhibitor_inv fork noOk run
  obtain ⟨_, run⟩ := excess_inv fork window run
  have read0 : (afterSload sevm b 0).getStorVal sevm.currentTarget 1 =
      b.getStorVal sevm.currentTarget 1 := afterSload_getStorVal sevm b 0 _ 1
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
theorem feePath_exact {revert getter submission : SFunc} {iterations : Nat} {finalOutput : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (window : fs[p.window]? = some (windowOf p getter submission))
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess p.target.word sevm b) 17 1 17 0
      iterations finalOutput)
    (tail : SFunc.RunExact fs sevm (St (feeBase sevm b) [finalOutput / (17 : B256)] M G)
      (selected sevm p.len.word getter submission) o) :
    SFunc.RunExact fs sevm (St b [] M (G + feePathGas sevm b iterations))
      (feePathTree p revert getter submission) o := by
  have read0 : (afterSload sevm b 0).getStorVal sevm.currentTarget 1 =
      b.getStorVal sevm.currentTarget 1 := afterSload_getStorVal sevm b 0 _ 1
  have hloop := fun finalCounter => (RequestFee.postloop_exact (len := p.len) (dest := p.submit)
    (w := p.len.word) (numerator := storedExcess p.target.word sevm b) (denominator := 17)
    (accumulator := 0) (output := finalOutput) (counter := finalCounter) (fs := fs) rfl
    (getter := getter) (submission := submission) tail)
  have hlooped := RequestFee.loop_exact loop fork.rules_push0 wordRun hloop
  have hinit := RequestFee.init_exact fork.rules_push0 hlooped
  have hwindow : SFunc.RunExact fs sevm
      (St (feeBase sevm b) [storedExcess p.target.word sevm b] M
        (G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1)) (windowOf p getter submission) o := by
    unfold windowOf windowTree
    refine rx_dest ?_
    refine rx_push (w := (17 : B256)) rfl (by change 1 < 1024; decide) ?_
    refine rx_swap1 ?_
    exact hinit
  have hexcess := excess_exact (b := afterSload sevm b 0) (target := p.target) (over := p.over)
    (under := p.under) (slot0 := b.getStorVal sevm.currentTarget 0) fork window (by
      rw [read0]
      exact hwindow)
  have hguard := inhibitor_exact (dest := p.revert) (revert := revert) fork off hexcess
  have hgas : G + feePathGas sevm b iterations =
      G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1 + 35 + sloadCost sevm (afterSload sevm b 0) 1 + 3
        + 22 + sloadCost sevm b 0 + 2 := by
    simp only [feePathGas, feePathFixedGas]
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

/-- Successful execution from an empty stack at a non-system caller enters the fee path. -/
theorem exec_user (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ G, SFunc.Run k.cert.prog sevm (St pre [] pre.memory G) k.user (.halted post) := by
  obtain ⟨f, hf, run⟩ := lift_sound k.check hcode fork exec
  rw [k.root] at hf
  cases hf
  rw [St.self stack rfl] at run
  obtain ⟨G, run⟩ := dispatch_inv run
  exact ⟨G, by simpa only [dispatchArm, ite_eq_right caller] using run⟩

/-- An exact fee path at a non-system caller is a successful execution of the bytes. -/
theorem exec_of_user (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress)
    (tail : SFunc.RunExact k.cert.prog sevm (St b [] M G) k.user (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) := by
  apply lift_exact k.check k.jumps hcode fork
  refine ⟨_, k.root, dispatch_exact ?_⟩
  simpa only [dispatchArm, ite_eq_right caller] using tail

/-- While slot 0 holds the inhibitor, no execution at a non-system caller succeeds, whatever the
calldata, value and memory. -/
theorem exec_inhibited_no_ok (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  obtain ⟨_, run⟩ := exec_user hcode fork stack caller exec
  exact (inhibitor_inv fork k.revert_noOk run).1 inhibited

/-- What a successful fee read does, for the fee recurrence's iteration count and final output. -/
structure FeeRead (target : B256) (sevm : Sevm) (pre post : Devm) (iterations : Nat)
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
  state : ∃ gas, post = RequestFee.feeGetterPost (feeBase sevm pre) pre.memory
    (finalOutput / (17 : B256)) gas

/-- The quoted word fee is at most `fake_exponential(1, excess, 17)` of the quoted excess. -/
theorem FeeRead.fee_le {target : B256} {iterations : Nat} {finalOutput : B256}
    (read : FeeRead target sevm pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat ≤ fakeExp 1 (storedExcess target sevm pre).toNat 17 :=
  RequestFeeWord.word_fee_le read.quote

/-- The quoted word fee equals the natural fee exactly on the recurrence's no-wrap domain. -/
theorem FeeRead.fee_eq_iff {target : B256} {iterations : Nat} {finalOutput : B256}
    (read : FeeRead target sevm pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 (storedExcess target sevm pre).toNat 17 ↔
      RequestFeeWord.NoWrapDomain (storedExcess target sevm pre) iterations :=
  RequestFeeWord.word_fee_eq_iff read.quote

private theorem feeBase_getStor (sevm : Sevm) (b : Devm) (a : Adr) :
    (feeBase sevm b).getStor a = b.getStor a := by
  simp only [feeBase, afterSload_getStor]

private theorem feeBase_getBal (sevm : Sevm) (b : Devm) (a : Adr) :
    (feeBase sevm b).getBal a = b.getBal a := by
  simp only [feeBase, Devm.getBal, afterSload_getAcct]

private theorem feeBase_logs (sevm : Sevm) (b : Devm) : (feeBase sevm b).logs = b.logs := by
  simp only [feeBase, afterSload_logs]

/-- A successful empty-calldata execution at a non-system caller is a fee read. -/
theorem exec_fee_read (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, FeeRead k.target sevm pre post iterations finalOutput := by
  obtain ⟨_, run⟩ := exec_user hcode fork stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, _, run⟩ :=
    feePath_inv k.shape fork k.revert_noOk k.window k.loop run
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  simp only [selected, ite_eq_right hlen] at run
  obtain ⟨_, zero, _, run⟩ := RequestFee.guard_inv k.getterRevert_noOk run
  obtain ⟨gas, rfl⟩ := RequestFee.return_inv aligned run
  have facts := RequestFee.feeGetterPost_facts (feeBase sevm pre) pre.memory
    (finalOutput / (17 : B256)) gas wf aligned
  refine ⟨iterations, finalOutput, zero, active, wordRun, facts.1, ?_, ?_, ?_, gas, rfl⟩
  · intro address
    rw [← feeBase_getStor sevm pre address]
    exact congrArg (fun world : World => (world.state.get address).stor) facts.2.1
  · intro address
    rw [← feeBase_getBal sevm pre address]
    exact congrArg (fun world : World => (world.state.get address).bal) facts.2.1
  · rw [← feeBase_logs sevm pre]
    exact (congrArg Meta.logs facts.2.2.1).trans rfl

/-- The charge of a fee read, from the frame's start. -/
def feeReadGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  RequestFee.feeGetterGas M + 30 + feePathGas sevm b iterations + dispatchGas

/-- The fee read forward: empty calldata, no value and slot 0 off the inhibitor give a successful
execution at the exact charge, returning the word recurrence's quotient. The recurrence always has
a finite run (`WordFakeExponential.run_exists`), so this premise can always be met. -/
theorem exec_fee_read_exact {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target sevm b) 17 1 17 0
      iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) := by
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  have hempty : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have body := RequestFee.guard_exact (dest := k.getterDest) (revert := k.getterRevert)
    (fs := k.cert.prog) hempty zero
    (RequestFee.return_exact (b := feeBase sevm b) (M := M) (G := G)
      (fee := finalOutput / (17 : B256)) fork.rules_push0 aligned)
  have path := feePath_exact k.shape (revert := k.revert) (submission := k.submission) fork
    k.window k.loop off wordRun
    (by simpa only [selected, ite_eq_right hlen] using body)
  have hgas : G + feeReadGas sevm b M iterations =
      (G + RequestFee.feeGetterGas M + 30 + feePathGas sevm b iterations) + dispatchGas := by
    simp only [feeReadGas, Nat.add_assoc]
  rw [hgas]
  exact exec_of_user hcode fork caller path

end UserPath

end Blanc.Lift.BuilderRequest
