import Blanc.LidoCircuitBreakerPauseWalk

/-!
# What is already true before the target gets control

Every Stage 5 statement about the pause was proved at a world with a
cooperative callee.  Some facts about a pause do not depend on the callee at
all, because they are settled **before the target ever executes**: `pause`
takes the reentrancy lock, checks the caller's assignment and liveness, and
runs the whole `setPauser` kernel — clearing the paused target's assignment
and emitting `PauserSet` — and only then reaches `pauseAfterSet`, which
performs the external CALL and STATICCALL.

The theorems here are about that prefix, and they are stated over an arbitrary
`base` world, an arbitrary target and arbitrary target bytecode: no hypothesis
below constrains the code at the paused address, and none can be discharged
only by a cooperating callee.

## What these do not say

* Nothing about what the target does, returns, or leaves behind.
* Nothing about the pause completing, succeeding, or reaching its expiry
  write.  A hostile callee can prevent all of that, and the published
  callback-visible liveness counterexample stands unchanged.
* Nothing about the CALL's arguments or the decoding of the target's answer.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The lock is held for the whole of the rest of the pause

`pause` opens `tload lockKey ::: iszero ::: (…taken… <?> …refuse…)`, so the
first thing a successful pause does is write `1` to the lock, and every state
downstream of `pauseLockPost` inherits it. -/

/-- Transient read-after-write at the same address and key.  The zero-valued
special case is transcribed privately in
`Blanc/LidoCircuitBreakerPauseWorldRun.lean`; this general form is the one the
pre-control statements need, and it is an upstream candidate. -/
theorem getTransVal_setTransVal_self (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setTransVal a k v).getTransVal a k = v := by
  show ((devm.transientStorage.setStorVal a k v).getD a .empty).get k = v
  unfold Tra.setStorVal
  rw [Std.TreeMap.getD_eq_getD_getElem?, Tra.getElem?_set, if_pos rfl]
  split
  · -- The pruning branch: the map after the write is empty, so the write's
    -- own read-back law already says the stored word is what an empty map
    -- reads at `k`.
    rename_i hpruned
    have hEmpty :
        (Std.TreeMap.getD devm.transientStorage a Stor.empty).set k v =
          Stor.empty :=
      Std.TreeMap.eq_empty_iff_isEmpty.mpr hpruned
    have hread := Stor.get_set_self
      (Std.TreeMap.getD devm.transientStorage a Stor.empty) k v
    rw [hEmpty] at hread
    exact hread
  · show ((Option.getD (some _)) Stor.empty).get k = v
    exact Stor.get_set_self _ _ _

/-- The lock is set at the state `pause` hands to its own body. -/
theorem pauseLockPost_lock (sevm : Sevm) (base : Devm) :
    (pauseLockPost sevm base).getTransVal sevm.currentTarget lockKey = 1 :=
  getTransVal_setTransVal_self _ _ _ _

/-! ## The lock survives to the kernel entry

`pause`'s three reads between taking the lock and entering the `setPauser`
kernel are `SLOAD`s.  A cold `SLOAD` only warms an accessed-key set, so none
of them touches transient storage and the lock is still held at the state the
kernel is entered from. -/

theorem temporalSloadBase_getTransVal (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) (k : B256) :
    (temporalSloadBase sevm base key).getTransVal a k =
      base.getTransVal a k := by
  unfold temporalSloadBase
  split
  · rfl
  · rfl

/-- The lock is held at the state `pause` hands the Registry kernel. -/
theorem pauseKernelBase_lock (sevm : Sevm) (base : Devm)
    (target pauser : B256) :
    (pauseKernelBase sevm base target pauser).getTransVal
      sevm.currentTarget lockKey = 1 := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getTransVal, temporalSloadBase_getTransVal,
    temporalSloadBase_getTransVal]
  exact pauseLockPost_lock sevm base

/-! ## The assignment is cleared before the kernel branches

`setPauserKernel` reads the target's assignment cell and immediately writes
`newPauserWord` into it, *before* the branch that separates the append arm
from the two removal arms.  `assignmentPost` is the substrate's name for that
post-write state, so the clearing is a fact about a named state on the common
prefix of every arm — no arm analysis is needed to establish it. -/

/-- Storage read-after-write at the same address and key.  Another upstream
candidate: the substrate uses this shape repeatedly but through per-site
rewrites rather than a named law. -/
theorem Devm.getStorVal_setStorVal_self (devm : Devm) (a : Adr) (k v : B256) :
    (devm.setStorVal a k v).getStorVal a k = v := by
  show ((devm.state.setStorVal a k v).get a).stor.get k = v
  unfold State.setStorVal
  rw [State.get_set_self]
  exact Stor.get_set_self _ _ _

theorem temporalSstorePost_getStorVal_self (sevm : Sevm) (base : Devm)
    (key value : B256) :
    (temporalSstorePost sevm base key value).getStorVal
      sevm.currentTarget key = value := by
  unfold temporalSstorePost
  exact Devm.getStorVal_setStorVal_self _ _ _ _

/-- The kernel's assignment write, read back.  For a pause this is invoked
with `newPauser = 0`, which is the clearing this goal is about; the statement
is left general because the same write serves registration. -/
theorem assignmentPost_assignment (sevm : Sevm) (base : Devm)
    (target newPauser : B256) :
    (assignmentPost sevm base target newPauser).getStorVal
      sevm.currentTarget (assignmentSlot target) = newPauser :=
  temporalSstorePost_getStorVal_self _ _ _ _

/-! ## P4: a re-entering pause is refused

The lock is taken *before* `pause` yields control, so the target that receives
control is looking at a CircuitBreaker whose lock is already set.  This is the
half that gives that fact its meaning: entered from such a state, `pause`
cannot get past its own reentrancy guard.

Nothing below constrains the code at any address.  `sevm` is arbitrary — an
arbitrary caller, an arbitrary `currentTarget`, arbitrary calldata — and
`target` is an arbitrary address-shaped word.  The only premises are about the
calldata the re-entering caller supplies and about the lock cell itself; a
hostile callee discharges them exactly as a cooperative one does.  In
particular this says nothing about the pause completing: the published
callback-visible liveness counterexample stands. -/

/-- Frame-local gas of a refused re-entrant `pause`, from the endpoint's entry
to its `REVERT`.

`21` for `requireStaticArgs 1` and `33` for `canonicalAddressArg 0`; `3` for
the lock key push, `100` for the `TLOAD` and `3` for the `ISZERO`; `13` for the
zero arm of the lock branch — a zero arm pays no `JUMPDEST`, which is the whole
difference from the taken arm's `14`; `12` for the `.call` burn and `17` for
`reentrantCallError`'s `revSelectorCost` against empty memory. -/
def pauseReentrantGas : Nat := 202

set_option maxRecDepth 16384 in
/-- A `pause` entered with the reentrancy lock already set takes the lock
guard's refusal arm and reverts with `ReentrantCall`'s own four-byte payload,
leaving storage, transient storage and the log list untouched. -/
theorem pause_body_runCompiledTo_error_of_locked
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (target : B256) (G : Nat)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hlocked : base.getTransVal sevm.currentTarget lockKey ≠ 0) :
    ∃ post,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm
        (base.setMach ⟨[], Mem.empty, G + pauseReentrantGas⟩)
        pause (.error (.revert, post)) ∧
      post.output = customErrorData "ReentrantCall" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      (∀ a k, post.getTransVal a k = base.getTransVal a k) := by
  let errData := customErrorData "ReentrantCall"
  refine ⟨(base.setMach
      ⟨[], Mem.empty.write 0 errData.toB256.toBytes, G⟩).withOutput errData,
    ?_, rfl, rfl, ?_, ?_⟩
  · unfold pauseReentrantGas pause requireStaticArgs canonicalAddressArg arg
      cdl checkNonAddress pushAddressMask
    func_run (12) [0, ~~~(0 : B256), addressMask, 0]
    case h_val =>
      rw [hdataLength]
      decide +kernel
    case h_val =>
      rw [show (32 * 0 + 4 : B256) = 4 by decide +kernel, hdataTarget]
      exact hmask
    case h_arm =>
      func_run (1)
      set total := G + 202 with htotal
      have htload : Ninst.RunCompiled sevm
          (base.setMach ⟨[lockKey], Mem.empty, total - 57⟩) Ninst.tload
          (base.setMach
            ⟨[base.getTransVal sevm.currentTarget lockKey], Mem.empty,
              total - 157⟩) := by
        have h := runCompiled_tload_of (sevm := sevm)
          (pre := base.setMach ⟨[lockKey], Mem.empty, total - 57⟩)
          (key := lockKey)
          (value := base.getTransVal sevm.currentTarget lockKey)
          (stack := []) (G := total - 157) rfl rfl
          (by simp only [Devm.gasLeft_setMach, gasWarmAccess, htotal]; omega)
          (by simp)
        simpa only [Devm.memory_setMach, Devm.setMach_setMach] using h
      refine Func.RunCompiledTo.next htload ?_
      func_run (3) [0]
      case h_val =>
        simp [B256.eqCheck, hlocked]
      case h_body =>
        apply Func.runCompiledTo_revSelector (G := G)
        · simp [customErrorData, B256.length_toBytes]
        · exact Mem.wf_empty
        · exact Mem.reads_empty
        · rfl
        · simp only [Devm.gasLeft_setMach, revSelectorCost]
          rw [Devm.extCost_empty_word]
          norm_num [gVerylow, gBase, gMemory]
          omega
        · simp only [Devm.stack_setMach, List.length_nil]
          omega
  · intro a k
    rfl
  · intro a k
    rfl

/-- The same refusal at the deployed runtime's own entry: a re-entering call
that reaches the CircuitBreaker while the lock is held reverts with
`ReentrantCall`, having written nothing.

The premises are the two `pause` needs of any caller — a well-formed
`pause(address)` calldata frame and no attached value — plus the identity of
the CircuitBreaker's *own* code.  Nothing constrains the code at `target`, or
at any other address: `target` is an arbitrary address-shaped word and `sevm`
carries an arbitrary caller.  A re-entrant call that is malformed, or that
attaches value, still reverts; it just reverts at an earlier guard, which is
why those two premises are here rather than dropped. -/
theorem pause_runCompiledTo_error_of_locked
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (target : B256) (G : Nat)
    (hdataLength : sevm.data.length = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "pause" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hmask : addressMask &&& target = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hlocked : base.getTransVal sevm.currentTarget lockKey ≠ 0) :
    ∃ post,
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty,
          G + pauseDispatchGas + pauseReentrantGas⟩)
        (runtime dp) (.error (.revert, post)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) ∧
      post.output = customErrorData "ReentrantCall" ∧
      post.logs = base.logs ∧
      (∀ a k, post.getStorVal a k = base.getStorVal a k) ∧
      (∀ a k, post.getTransVal a k = base.getTransVal a k) := by
  obtain ⟨post, hbody, hout, hlogs, hstor, htrans⟩ :=
    pause_body_runCompiledTo_error_of_locked dp sevm base target G
      hdataLength hmask hdataTarget hlocked
  obtain ⟨hprog, hcompile⟩ :=
    pause_dispatch_runCompiledTo dp sevm base pauseReentrantGas G
      (.error (.revert, post)) hdataLength hvalue hselector hcodeAddress
      hcode hbody
  exact ⟨post, hprog, hcompile, hout, hlogs, hstor, htrans⟩

end Blanc.LidoCircuitBreaker
