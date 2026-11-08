import Blanc.Lift.RequestFee.Getter
import Blanc.Lift.RequestSystem.Dispatch
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.PackedSha
import Blanc.Lift.ExactWalkSolc
import Blanc.ForwardStorageAccess
import Blanc.RequestFeeWord
import Blanc.RequestFeeWordDomain

/-!
# The plain request contracts' user path, under covered forks

The EIP-7002 and EIP-7251 runtimes share one user path up to the calldata-length branch: caller
dispatch, `PUSH1 17`, the slot-zero inhibitor guard, and the shared fee window run on slot 0 as it
is stored. Unlike the EIP-8282 builder codes there is no adjustment by the count over target, so the
quoted excess is the stored word. Only the pushed jump targets, the calldata length and the
continuation trees differ, so a generated tree is an instance of `plainPathTree` by `rfl`. After the
calldata-length branch, the submission arm starts with the value guard `paidTree`.

These are statements about one frame's walk over any storage, under covered forks. Nothing here says
which storage is reachable. EIP-7002 keeps its own glue (`WithdrawalRequest.UserSetup`,
`WithdrawalRequest.UserFeeDispatch`), which its pinned statements reach.
-/

namespace Blanc.Lift.RequestFee

open Jaune
open RequestSystem (dispatchTree dispatchArm dispatchGas dispatch_exact system_push)

/-- `PUSH1 17; PUSH0; SLOAD; DUP1; PUSH32 MAX; EQ; PUSH dest; JUMPI`: revert when slot 0 is the
inhibitor, else fall into `active` with `[slot0, 17]` on the stack. -/
def plainGuardTree (dest : PushWord) (active revert : SFunc) : SFunc :=
  (.next (.push [0x11] (by decide)) (.next (.push [] (by decide)) (.next (.reg .sload)
  (.next (.reg (.dup 0))
  (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff] (by decide)) (.next (.reg .eq)
  (.next (.push (dest.head :: dest.tail) dest.le) (.branch active revert))))))))

/-- `JUMPDEST; CALLVALUE; LT; PUSH dest; JUMPI`: revert when the value is below the fee on the stack. -/
def paidTree (dest : PushWord) (body revert : SFunc) : SFunc :=
  (.dest (.next (.reg .callvalue) (.next (.reg .lt)
  (.next (.push (dest.head :: dest.tail) dest.le) (.branch body revert)))))

/-- The pushed words and program entries a plain contract's user path differs by. -/
structure PlainShape where
  /-- Destination of the inhibitor's revert. -/
  revert : PushWord
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

/-- The user path from the inhibitor guard to the calldata-length branch. -/
def plainPathTree (p : PlainShape) (revert getter submission : SFunc) : SFunc :=
  plainGuardTree p.revert
    (initTree (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission))) revert

/-- The fixed charge of the guard: `PUSH1`, `PUSH0`, `DUP1`, `PUSH32`, `EQ`, `PUSH`, `JUMPI`. -/
def plainGuardFixedGas : Nat := 5 * gVerylow + gBase + gHigh

theorem plainGuardFixedGas_eq : plainGuardFixedGas = 27 := rfl

/-- The guard's charge, with slot 0's cold or warm read. -/
def plainGuardGas (sevm : Sevm) (b : Devm) : Nat := plainGuardFixedGas + sloadCost sevm b 0

/-- The exact charge of `plainPathTree` up to the selected continuation. -/
def plainPathGas (sevm : Sevm) (b : Devm) (iterations : Nat) : Nat :=
  postloopFixedGas + feeLoopGas iterations + 19 + plainGuardGas sevm b

/-- The value guard's charge. -/
def paidGas : Nat := gJumpdest + gBase + 2 * gVerylow + gHigh

theorem paidGas_eq : paidGas = 19 := rfl

/-- A read's base keeps the world's state. -/
theorem afterSload_state (sevm : Sevm) (b : Devm) (k : B256) : (afterSload sevm b k).state = b.state := by
  unfold afterSload
  split <;> rfl

theorem afterSload_getBal (sevm : Sevm) (b : Devm) (k : B256) (a : Adr) :
    (afterSload sevm b k).getBal a = b.getBal a := by
  show ((afterSload sevm b k).state.get a).bal = (b.state.get a).bal
  rw [afterSload_state]

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- A successful dispatch at a non-system caller reaches the user arm, on the same stack and memory. -/
theorem dispatch_user_inv {dest : PushWord} {user system : SFunc} (caller : sevm.caller ≠ systemAddress)
    (run : SFunc.Run fs sevm (St b [] M G) (dispatchTree dest user system) o) :
    ∃ G', SFunc.Run fs sevm (St b [] M G') user o := by
  have run := run.cut
  unfold dispatchTree at run
  winv 2
  rw [system_push] at run
  winv 1
  rw [adr_eqCheck, ite_eq_right caller] at run
  winv 1
  rcases ric_branch run with ⟨_, G', run⟩ | ⟨flag, _, _⟩
  · exact ⟨G', run.uncut⟩
  · exact absurd rfl flag

/-- A certified runtime whose root is caller dispatch: an exact run of the user arm at a non-system
caller is a successful execution of the bytes, at the arm's charge plus the dispatch's. -/
theorem exec_of_dispatch_user {code : ByteArray} {c : Cert} {dest : PushWord} {user system : SFunc}
    {post : Devm} (check : Cert.check code c = true) (jumps : Cert.jumpsOk code c = true)
    (noExec : ProgNoExec c.prog) (root : c.prog[0]? = some (dispatchTree dest user system))
    (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress)
    (tail : SFunc.RunExact c.prog sevm (St b [] M G) user (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) :=
  lift_exact_noExec check jumps hcode noExec
    ⟨_, root, dispatch_exact (by simpa only [dispatchArm, ite_eq_right caller] using tail)⟩

/-- A run past the guard has slot 0 off the inhibitor, and enters `active` on `[slot0, 17]`. -/
theorem plainGuard_inv (fork : CoveredFork sevm.benvStat.fork) {dest : PushWord} {active revert : SFunc}
    (noOk : revert.noOk = true)
    (run : SFunc.Run fs sevm (St b [] M G) (plainGuardTree dest active revert) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
      ∃ G', SFunc.Run fs sevm
        (St (afterSload sevm b 0) [b.getStorVal sevm.currentTarget 0, 17] M G') active o := by
  have run := run.cut
  unfold plainGuardTree at run
  winv 2
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
theorem plainGuard_exact (fork : CoveredFork sevm.benvStat.fork) {dest : PushWord} {active revert : SFunc}
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (tail : SFunc.RunExact fs sevm
      (St (afterSload sevm b 0) [b.getStorVal sevm.currentTarget 0, 17] M G) active o) :
    SFunc.RunExact fs sevm (St b [] M (G + plainGuardGas sevm b)) (plainGuardTree dest active revert) o := by
  have hgas : G + plainGuardGas sevm b = G + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 + 3 := by
    simp only [plainGuardGas, plainGuardFixedGas_eq]
    omega
  rw [hgas]
  unfold plainGuardTree
  refine rx_push (w := (17 : B256)) rfl (by decide) ?_
  refine rx_push0 (h_push0 := CoveredFork.rules_push0 fork) (by change 1 < 1024; decide) ?_
  refine rx_sload_sel fork (by change 1 < 1024; decide) ?_
  refine rx_dup1 (by change 2 < 1024; decide) ?_
  refine rx_push inhibitor_push (by change 3 < 1024; decide) ?_
  refine rx_eq (v := 0) ?_ (by change 2 < 1024; decide) ?_
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm off)]
  · refine rx_push rfl (by change 3 < 1024; decide) ?_
    exact rx_branch_zero tail

/-- Success passes the value guard. -/
theorem paid_inv {dest : PushWord} {body revert : SFunc} {fee : B256} (noOk : revert.noOk = true)
    (run : SFunc.Run fs sevm (St b [fee] M G) (paidTree dest body revert) o) :
    fee.toNat ≤ sevm.value.toNat ∧ ∃ G', SFunc.Run fs sevm (St b [] M G') body o := by
  have run := run.cut
  unfold paidTree at run
  winv 4
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨_, _, run⟩
  · exact ⟨toNat_ge_of_ltCheck_eq_zero flag, G', run.uncut⟩
  · exact False.elim (run.false_of_noOk noOk)

/-- The value guard, forward, at its exact charge. -/
theorem paid_exact {dest : PushWord} {body revert : SFunc} {fee : B256}
    (covered : fee.toNat ≤ sevm.value.toNat)
    (tail : SFunc.RunExact fs sevm (St b [] M G) body o) :
    SFunc.RunExact fs sevm (St b [fee] M (G + paidGas)) (paidTree dest body revert) o := by
  have notLow : ¬ sevm.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge covered
  have hgas : G + paidGas = G + 10 + 3 + 3 + 2 + 1 := by
    simp only [paidGas_eq]
  rw [hgas]
  unfold paidTree
  refine rx_dest ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by change 0 < 1024; decide) ?_
  · simp only [B256.ltCheck, ite_eq_right notLow]
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact rx_branch_zero tail

/-- A successful run of the plain user path passes the guard, runs the word fee recurrence on slot 0
as stored, and reaches the branch the calldata length selects with the quotient on the stack. -/
theorem plainPath_inv (fork : CoveredFork sevm.benvStat.fork) {p : PlainShape}
    {revert getter submission : SFunc} (noOk : revert.noOk = true)
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (run : SFunc.Run fs sevm (St b [] M G) (plainPathTree p revert getter submission) o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      ∃ G', SFunc.Run fs sevm (St (afterSload sevm b 0) [finalOutput / (17 : B256)] M G')
        (selected sevm p.len.word getter submission) o := by
  obtain ⟨active, _, run⟩ := plainGuard_inv fork noOk run
  obtain ⟨iterations, finalOutput, wordRun, _⟩ :=
    WordFakeExponential.run_exists (b.getStorVal sevm.currentTarget 0) 17 1 17 0
  refine ⟨active, iterations, finalOutput, wordRun, ?_⟩
  obtain ⟨_, run⟩ := init_inv run
  obtain ⟨_, _, run⟩ := loop_inv loop wordRun run
  exact postloop_inv rfl run

/-- The plain user path, forward: the selected continuation transports back at the exact charge. -/
theorem plainPath_exact (fork : CoveredFork sevm.benvStat.fork) {p : PlainShape}
    {revert getter submission : SFunc} {iterations : Nat} {finalOutput : B256}
    (loop : fs[p.loopEntry]? =
      some (loopTree p.post p.loop p.loopEntry (postloopTree p.len p.submit getter submission)))
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0
      iterations finalOutput)
    (tail : SFunc.RunExact fs sevm (St (afterSload sevm b 0) [finalOutput / (17 : B256)] M G)
      (selected sevm p.len.word getter submission) o) :
    SFunc.RunExact fs sevm (St b [] M (G + plainPathGas sevm b iterations))
      (plainPathTree p revert getter submission) o := by
  have hloop := fun finalCounter => (postloop_exact (len := p.len) (dest := p.submit)
    (w := p.len.word) (numerator := b.getStorVal sevm.currentTarget 0) (denominator := 17)
    (accumulator := 0) (output := finalOutput) (counter := finalCounter) (fs := fs) rfl
    (getter := getter) (submission := submission) tail)
  have hlooped := loop_exact loop (CoveredFork.rules_push0 fork) wordRun hloop
  have hinit := init_exact (CoveredFork.rules_push0 fork) hlooped
  have hguard := plainGuard_exact fork (dest := p.revert) (revert := revert) off hinit
  have hgas : G + plainPathGas sevm b iterations =
      G + 45 + feeLoopGas iterations + 19 + plainGuardGas sevm b := by
    simp only [plainPathGas, postloopFixedGas_eq]
    omega
  rw [hgas]
  exact hguard

/-- A plain runtime's user path: a checked certificate whose root is caller dispatch into
`plainPathTree`, whose empty-calldata arm is the shared getter. -/
structure PlainUserPath where
  /-- The runtime bytes. -/
  code : ByteArray
  /-- Its certificate. -/
  cert : Cert
  check : Cert.check code cert = true
  jumps : Cert.jumpsOk code cert = true
  /-- No node of the certificate is a call-family instruction. -/
  noExec : ProgNoExec cert.prog
  /-- The pushed words of the user path. -/
  shape : PlainShape
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
    (plainPathTree shape revert (guardTree getterDest returnTree getterRevert) submission) system)
  loop : cert.prog[shape.loopEntry]? = some (loopTree shape.post shape.loop shape.loopEntry
    (postloopTree shape.len shape.submit (guardTree getterDest returnTree getterRevert) submission))
  revert_noOk : revert.noOk = true
  getterRevert_noOk : getterRevert.noOk = true
  len_ne : shape.len.word ≠ 0

namespace PlainUserPath

variable (k : PlainUserPath)

/-- The getter arm. -/
abbrev getter : SFunc := guardTree k.getterDest returnTree k.getterRevert

/-- The user arm of caller dispatch. -/
abbrev user : SFunc := plainPathTree k.shape k.revert k.getter k.submission

variable {k} {pre post : Devm}

/-- Successful execution from an empty stack at a non-system caller enters the user path. -/
theorem exec_user (hcode : sevm.code = k.code) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    ∃ G, SFunc.Run k.cert.prog sevm (St pre [] pre.memory G) k.user (.halted post) := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec k.check hcode k.noExec exec
  rw [k.root] at hf
  cases hf
  rw [St.self stack rfl] at run
  exact dispatch_user_inv caller run

/-- An exact user path at a non-system caller is a successful execution of the bytes. -/
theorem exec_of_user (hcode : sevm.code = k.code) (caller : sevm.caller ≠ systemAddress)
    (tail : SFunc.RunExact k.cert.prog sevm (St b [] M G) k.user (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) :=
  exec_of_dispatch_user k.check k.jumps k.noExec k.root hcode caller tail

/-- While slot 0 holds the inhibitor, no execution at a non-system caller succeeds, whatever the
calldata, value and memory. -/
theorem exec_inhibited_no_ok (fork : CoveredFork sevm.benvStat.fork) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  exact (plainGuard_inv fork k.revert_noOk run).1 inhibited

/-- What a successful fee read does, for the fee recurrence's iteration count and final output. -/
structure FeeRead (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop where
  /-- The read carried no value. -/
  value : sevm.value = 0
  /-- Slot 0 is not the inhibitor. -/
  active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The word recurrence ran on slot 0 as stored. -/
  quote : WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput
  /-- The return bytes are the quotient, as one word. -/
  output : post.output = (finalOutput / (17 : B256)).toBytes
  /-- No account's storage changed. -/
  storage : ∀ address, post.getStor address = pre.getStor address
  /-- No balance changed. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- No log was appended. -/
  logs : post.logs = pre.logs
  /-- The whole post state: slot 0 warmed, the word in memory, the rest unchanged. -/
  state : ∃ gas, post = feeGetterPost (afterSload sevm pre 0) pre.memory (finalOutput / (17 : B256)) gas

/-- The quoted word fee is at most `fake_exponential(1, excess, 17)` of the stored excess. -/
theorem FeeRead.fee_le {iterations : Nat} {finalOutput : B256}
    (read : FeeRead sevm pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat ≤ fakeExp 1 (pre.getStorVal sevm.currentTarget 0).toNat 17 :=
  RequestFeeWord.word_fee_le read.quote

/-- The quoted word fee equals the natural fee exactly on the recurrence's no-wrap domain. -/
theorem FeeRead.fee_eq_iff {iterations : Nat} {finalOutput : B256}
    (read : FeeRead sevm pre post iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 (pre.getStorVal sevm.currentTarget 0).toNat 17 ↔
      RequestFeeWord.NoWrapDomain (pre.getStorVal sevm.currentTarget 0) iterations :=
  RequestFeeWord.word_fee_eq_iff read.quote

private theorem post_facts {pre : Devm} {M : Mem} {fee : B256} {gas : Nat} (wf : Mem.Wf M)
    (aligned : M.size % 32 = 0) :
    (feeGetterPost (afterSload sevm pre 0) M fee gas).output = fee.toBytes ∧
    (∀ a, (feeGetterPost (afterSload sevm pre 0) M fee gas).getStor a = pre.getStor a) ∧
    (∀ a, (feeGetterPost (afterSload sevm pre 0) M fee gas).getBal a = pre.getBal a) ∧
    (feeGetterPost (afterSload sevm pre 0) M fee gas).logs = pre.logs := by
  have facts := feeGetterPost_facts (afterSload sevm pre 0) M fee gas wf aligned
  refine ⟨facts.1, ?_, ?_, ?_⟩
  · intro address
    rw [← afterSload_getStor sevm pre 0 address]
    exact congrArg (fun world : World => (world.state.get address).stor) facts.2.1
  · intro address
    rw [← afterSload_getBal sevm pre 0 address]
    exact congrArg (fun world : World => (world.state.get address).bal) facts.2.1
  · rw [← afterSload_logs sevm pre 0]
    exact (congrArg Meta.logs facts.2.2.1).trans rfl

/-- A successful empty-calldata execution at a non-system caller is a fee read. -/
theorem exec_fee_read (fork : CoveredFork sevm.benvStat.fork) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, FeeRead sevm pre post iterations finalOutput := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, _, run⟩ :=
    plainPath_inv fork k.revert_noOk k.loop run
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  simp only [selected, ite_eq_right hlen] at run
  obtain ⟨_, zero, _, run⟩ := guard_inv k.getterRevert_noOk run
  obtain ⟨gas, rfl⟩ := return_inv aligned run
  obtain ⟨output, storage, balance, logs⟩ :=
    post_facts (sevm := sevm) (pre := pre) (fee := finalOutput / (17 : B256)) (gas := gas) wf aligned
  exact ⟨iterations, finalOutput, zero, active, wordRun, output, storage, balance, logs, gas, rfl⟩

/-- The charge of a fee read, from the frame's start. -/
def feeReadGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  feeGetterGas M + getterGuardGas + plainPathGas sevm b iterations + dispatchGas

/-- The fee read forward: empty calldata, no value and slot 0 off the inhibitor give a successful
execution at the exact charge, returning the word recurrence's quotient. The recurrence always has a
finite run (`WordFakeExponential.run_exists`), so this premise can always be met. -/
theorem exec_fee_read_exact {iterations : Nat} {finalOutput : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (hcode : sevm.code = k.code) (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0
      iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + feeReadGas sevm b M iterations))
      (.ok (feeGetterPost (afterSload sevm b 0) M (finalOutput / (17 : B256)) G))) := by
  have hlen : sevm.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  have hempty : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have body := guard_exact (dest := k.getterDest) (revert := k.getterRevert)
    (fs := k.cert.prog) hempty zero
    (return_exact (b := afterSload sevm b 0) (M := M) (G := G)
      (fee := finalOutput / (17 : B256)) (CoveredFork.rules_push0 fork) aligned)
  have path := plainPath_exact fork (p := k.shape) (revert := k.revert) (submission := k.submission)
    k.loop off wordRun (by simpa only [selected, ite_eq_right hlen] using body)
  have hgas : G + feeReadGas sevm b M iterations =
      (G + feeGetterGas M + 30 + plainPathGas sevm b iterations) + dispatchGas := by
    simp only [feeReadGas, getterGuardGas_eq, Nat.add_assoc]
  rw [hgas]
  exact exec_of_user hcode caller path

/-- **The fork of a user frame.** A successful execution at a non-system caller from an empty stack
passes the guard, quotes the fee on slot 0, and either reaches the submission arm at the submission's
length, or is a fee read on empty calldata. `lengthBound` holds of any calldata a frame can carry,
since `CALLDATASIZE` is read as a word. -/
theorem exec_user_cases (fork : CoveredFork sevm.benvStat.fork) (hcode : sevm.code = k.code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) :
    (pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧ sevm.data.length = k.shape.len.word.toNat ∧
      ∃ iterations finalOutput,
        WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations
          finalOutput ∧
        ∃ G0, SFunc.Run k.cert.prog sevm
          (St (afterSload sevm pre 0) [finalOutput / (17 : B256)] pre.memory G0)
          k.submission (.halted post)) ∨
    (sevm.data = [] ∧ ∃ iterations finalOutput, FeeRead sevm pre post iterations finalOutput) := by
  obtain ⟨_, run⟩ := exec_user hcode stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, G0, run⟩ :=
    plainPath_inv fork k.revert_noOk k.loop run
  by_cases hword : sevm.data.length.toB256 = k.shape.len.word
  · left
    have literal : sevm.data.length = k.shape.len.word.toNat := by
      have values := congrArg B256.toNat hword
      rwa [B256.toNat_toB256_of_lt lengthBound] at values
    rw [selected, ite_eq_left hword] at run
    exact ⟨active, literal, iterations, finalOutput, wordRun, G0, run⟩
  · right
    rw [selected, ite_eq_right hword] at run
    obtain ⟨empty, _, _⟩ := guard_inv k.getterRevert_noOk run
    have literal : sevm.data = [] := by
      have values := congrArg B256.toNat empty
      rw [B256.toNat_toB256_of_lt lengthBound] at values
      exact List.eq_nil_of_length_eq_zero values
    exact ⟨literal, exec_fee_read fork hcode stack aligned wf caller literal exec⟩

end PlainUserPath

/-! ## The word fee against `fake_exponential`, on the stored excess -/

/-- Through excess 2892, the quoted word fee is `fake_exponential(1, excess, 17)`. -/
theorem word_fee_eq_of_le {excess : B256} {iterations : Nat} {finalOutput : B256}
    (le : excess.toNat ≤ 2892)
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat = fakeExp 1 excess.toNat 17 := by
  rw [← toB256_toNat excess] at run
  exact RequestFeeWord.word_fee_eq_natural le run

/-- At excess 2893, the quoted word fee is not `fake_exponential(1, 2893, 17)`. -/
theorem word_fee_ne_at_2893 {excess : B256} {iterations : Nat} {finalOutput : B256}
    (at2893 : excess.toNat = 2893)
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput) :
    (finalOutput / (17 : B256)).toNat ≠ fakeExp 1 excess.toNat 17 := by
  rw [← toB256_toNat excess, at2893] at run
  rw [at2893]
  exact RequestFeeWord.word_fee_ne_natural_2893 run

/-- At excess 0 the fee recurrence takes one step and quotes 1 wei. -/
theorem word_run_zero : WordFakeExponential.Run 0 17 1 17 0 1 17 :=
  WordFakeExponentialEval.run_of_runFuel (fuel := 2) (by decide +kernel)

end Blanc.Lift.RequestFee
