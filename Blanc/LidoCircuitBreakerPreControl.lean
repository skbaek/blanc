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

end Blanc.LidoCircuitBreaker
