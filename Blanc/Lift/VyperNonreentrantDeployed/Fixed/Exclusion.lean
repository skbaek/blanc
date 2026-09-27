import Blanc.OwnerDiscipline
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.LockDominance

/-!
# V+: reentrancy exclusion for the corrected comparator 0x847e

The corrected Vyper 0.3.7 Curve plain-pool implementation
`I = 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9` (runtime `code`,
`Fixed/Cert.lean`) guards seven functions with one lock (slot `0`, held word
`2`; `Fixed/LockSpec.lean`).  This module instantiates the generic
`LockExclusion.LockSpec.lock_exclusion` (`Blanc/LockExclusion.lean`) for that
lock and discharges every per-code and per-owner hypothesis from theorems:

* `LockSpec.Dominance` is `lock_dominance` (the lock certificate,
  `Fixed/LockDominance.lean`);
* `LockSpec.OwnerDiscipline` is `Exec.ownerDiscipline_of_world`
  (`Blanc/OwnerDiscipline.lean`) for a storage owner `P` whose code is the
  comparator runtime or the 45-byte EIP-1167 forwarder to `I`;
* the forwarder premise `Exec.NoDelegateFrom` (no frame running `code`
  executes `DELEGATECALL`/`CALLCODE`) is `noDelegateFrom`, from the
  certificate cursor (`Blanc/Lift/Cursor.lean`), with no hash premise.

## What `vplus_exclusion` states, in words

Universally quantified: every execution `R : Exec 0 sevm pre out` of *any*
outcome (success, revert, exceptional halt), every raw frame root `F` of `R`
(the raw chronology `Exec.rawFrameRoots`, never committed/successful frames),
every node `h` of `F`'s frame at which `F` is active, every child `c` that `h`
spawns — whether `h`'s frame then resumes (`Spawns.runOk`) or fails to resume
(`Spawns.runErr`) — and every raw frame root `G` at or below `c`, whatever
each of them does afterwards.  Callback schedules are not a parameter: every
frame below `c`, with any code at any address, is covered by `R` itself.

Active (`ActiveRel`, the release-pc form of the master's disposition A2):
`F` is a pc-0 frame owned by `P` running `code`, it reached one of the five
mutating body starts `b` (after the lock-set `SSTORE`), and no node from `b`
up to (excluding) `h` sits at one of the five release pcs.

Conclusion: `G` is not a `P`-owned frame running `code` that reaches any of
the seven guarded body starts (the five mutating ones and the two guarded
views `price_oracle`, `get_virtual_price`).  `G` is not required to succeed;
reaching the pc is enough.

Assumed (world and trace facts only):
* `hfork`: the top frame runs on a fork Jaune covers (current-fork semantics).
* `hP`: in the pre-state, `P` holds the comparator runtime or the forwarder to
  `I`; `hI`: `I` holds the comparator runtime.
* `hroot`: if the top frame is owned by `P`, it runs the code stored at `P`
  (true of every message call; it only excludes an ill-formed root).
* `hash` (`HashAvoidIn`): every `KECCAK256` actually executed in a `P`-owned
  frame running `code` in `R` yields a digest other than slot `0`.  It
  constrains the executed hashes of this trace only, never all inputs of a
  shape, and says nothing about callees or attackers.

No premise mentions callbacks, reentry, the lock value seen by a callee, or
guarded bodies: exclusion is derived, not assumed.

Not claimed (statement boundary B1): reentry into a mutating function while
only a guarded view is running (Vyper 0.3.7 views never take the lock).  No
concrete pool address is fixed here; `vplus_exclusion_impl` is the instance
`P = I`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed

open Jaune Blanc.LockExclusion
open Jaune.Exec.Deriv (ParentPrefix)

theorem code_size : code.size = 18320 := by decide +kernel

theorem code_pos : 0 < code.size := by rw [code_size]; decide

theorem code_not_delegation : ¬ isValidDelegation code := fun h => by
  have := h.1
  rw [code_size] at this
  simp [eoaDelegatedCodeLength] at this

/-- No frame of an execution that runs the comparator executes `DELEGATECALL`
or `CALLCODE` (from the certificate cursor; no hash premise). -/
theorem noDelegateFrom {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) :
    Exec.NoDelegateFrom R code := by
  intro F hF hcode n hp
  obtain ⟨hpc, hfF⟩ := rawFrameRoots_entry R hfork hF
  obtain ⟨κ, -, ok⟩ := Blanc.Lift.cursor_of_parentPrefix cert_check hpc hcode hfF hp
  have hs := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hp
  have key : ∀ x, Xinst.At code n.pc x → x = .call ∨ x = .staticcall := fun x hat =>
    ok.exec_call_or_staticcall (by rw [hs, hcode]; exact hat)
  constructor
  · intro hat
    rcases key _ hat with h | h <;> cases h
  · intro hat
    rcases key _ hat with h | h <;> cases h

/-- Activity from lock set to lock release: the frame `F` of `P` running
`code` reached a mutating body start `b`, and no node from `b` to before `h`
is at a release pc. -/
def ActiveRel (P : Adr) (F h : Exec.Deriv) : Prop :=
  CPFrame P code F ∧ ParentPrefix F h ∧
    ∃ b, ParentPrefix F b ∧ ParentPrefix b h ∧ b.pc ∈ lockMutBodies ∧
      ∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h → x.pc ∉ lockReleasePcs

/-- The release-pc form implies the generic `Active` (first slot write), by
the strong dominance form. -/
theorem ActiveRel.active {sevm : Sevm} {pre : Devm} {out : Execution}
    {R : Exec 0 sevm pre out} (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hash : lockL.HashAvoidIn P R) {F h : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (a : ActiveRel P F h) : lockL.Active P F h := by
  obtain ⟨cp, hFh, b, hFb, hbh, hmb, norel⟩ := a
  obtain ⟨-, hfF⟩ := rawFrameRoots_entry R hfork hF
  refine ⟨cp, hFh, b, hFb, hbh, hmb, fun x hbx hxh hne hst => norel x hbx hxh hne ?_⟩
  exact lock_dominance_strong cp.1 hfF cp.2.2 (hash F hF cp) hFb hbx hmb hst

/-- Owner discipline for a storage owner holding the comparator or its
forwarder. -/
theorem ownerDiscipline {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hP : pre.getCode P = forwarderCode curvePlainImpl847e ∨ pre.getCode P = code)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = P → sevm.code = pre.getCode P) :
    lockL.OwnerDiscipline P R :=
  Exec.ownerDiscipline_of_world R lockL forwarderShape_847e noSstore_forwarder_847e
    code_pos code_not_delegation hP hI (fun h => by rw [hroot h]; exact hP)
    (noDelegateFrom R hfork)

/-- **V+ for the corrected comparator 0x847e.**  See the module docstring for
the statement in words. -/
theorem vplus_exclusion {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hP : pre.getCode P = forwarderCode curvePlainImpl847e ∨ pre.getCode P = code)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = P → sevm.code = pre.getCode P)
    (hash : lockL.HashAvoidIn P R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : ActiveRel P F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ lockL.Enters P G :=
  LockSpec.lock_exclusion (L := lockL) (P := P) R hfork lock_dominance (ownerDiscipline R hfork hP hI hroot)
    hash hF (active.active hfork hash hF) spawn hG

/-- V+ for the implementation address itself (`P = I`, no forwarder). -/
theorem vplus_exclusion_impl {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = curvePlainImpl847e →
      sevm.code = pre.getCode curvePlainImpl847e)
    (hash : lockL.HashAvoidIn curvePlainImpl847e R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : ActiveRel curvePlainImpl847e F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ lockL.Enters curvePlainImpl847e G :=
  vplus_exclusion R hfork (Or.inr hI) hI hroot hash hF active spawn hG

/-- The Curve ETH/stETH plain pool `0x21e27a5e5513d6e65c4f830167390997aa84843a` (factory
`0xB9fC157394Af804a3578134A6585C0dc9cc990d4`, pool index 303): a deployed EIP-1167 forwarder
to the comparator implementation `curvePlainImpl847e`.  Its runtime bytes are provenance
(read from three public operators), not a theorem; the premise `hP` below restates them. -/
def curveStethPool847e : Adr := 0x21e27a5e5513d6e65c4f830167390997aa84843a

/-- V+ for the deployed ETH/stETH pool behind the comparator. -/
theorem vplus_exclusion_stethPool {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hP : pre.getCode curveStethPool847e = forwarderCode curvePlainImpl847e)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = curveStethPool847e →
      sevm.code = pre.getCode curveStethPool847e)
    (hash : lockL.HashAvoidIn curveStethPool847e R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : ActiveRel curveStethPool847e F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ lockL.Enters curveStethPool847e G :=
  vplus_exclusion R hfork (Or.inl hP) hI hroot hash hF active spawn hG

end Blanc.Lift.VyperNonreentrantDeployed.Fixed
