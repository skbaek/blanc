import Blanc.Lift.FrameWalkKit
import Blanc.Lift.Curve3Pool.CheckTries
import Blanc.Lift.NodeWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Vyper
import Blanc.Lift.VyperRawCall
import Blanc.Lift.InvWalkGas
import Blanc.Lift.IdentityCallGas
import Blanc.Lift.Curve3Pool.Observe

/-!
# Walking the 3pool's actual derivation: decoding and one-step tactics

Every walk of a pool frame steps the frame's actual derivation (`XAt`, `Blanc/Lift/FrameWalk.lean`)
one instruction at a time. The instruction at each pc is decoded from the runtime's byte tries
(`codeTries`, `decodeT_sound`): `atN`/`atJ`/`atL` turn a decode equation, which elaboration
solves by evaluation (`by rfl`), into the `Ninst.At`/`Jinst.At`/`Linst.At` fact the step lemma
takes.

The tactics read the hypotheses `hcode : sevm.code = code`, `hfork : CoveredFork …` and the
walk state `h : XAt sevm post pc (St b S M G) L` by name, and replace `h` in place:

* `xn` — one non-spawning instruction, inverted by the matching `ri_*` lemma;
* `xjd` — a `JUMPDEST`; `xjmp` — a `JUMP`;
* `xji hw` — a `JUMPI`, splitting on its condition (`hw` names the condition fact);
* `xdead` — the rest of a reverting arm (`PUSH1 0; DUP1; REVERT` and the like) closes the goal.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.Lift.NodeWalk

variable {sevm : Sevm} {pc : Nat}

theorem atN {n : Ninst} (hcode : sevm.code = code)
    (h : decodeT 15 codeTries.bytes pc = some (.next n)) : Ninst.At sevm.code pc n := by
  rw [hcode]
  exact decodeT_sound codeTries h

theorem atJ {j : Jinst} (hcode : sevm.code = code)
    (h : decodeT 15 codeTries.bytes pc = some (.jump j)) : Jinst.At sevm.code pc j := by
  rw [hcode]
  exact decodeT_sound codeTries h

theorem atL {l : Linst} (hcode : sevm.code = code)
    (h : decodeT 15 codeTries.bytes pc = some (.last l)) : Linst.At sevm.code pc l := by
  rw [hcode]
  exact decodeT_sound codeTries h


set_option hygiene false in
/-- One non-spawning instruction `n` of the walk `h`, landing at `pc'`, inverted by the stack
lemma `ri` (`ri s : ∃ G', d = St …`). -/
macro "xs " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := $ri s
  clear s))

set_option hygiene false in
/-- As `xs`, for a lemma with one more witness (`∃ z G', d = St …`). -/
macro "xs2 " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, _, rfl⟩ := $ri s
  clear s))

set_option hygiene false in
/-- As `xs`, for a memory lemma over the image carrier `hR`, `hW`. -/
macro "xm " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := $ri hR hW s
  clear s hR hW
  obtain ⟨M, _, rfl, hR, hW⟩ := e))

set_option hygiene false in
/-- As `xm`, with the memory offset normalized to `o` (and, for `CALLDATACOPY`, the size). -/
macro "xmo " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := $ri hR hW s
  clear s hR hW
  obtain ⟨M, _, rfl, hR, hW⟩ := e))

set_option hygiene false in
/-- As `xs`, for a storage lemma (`hfork`). -/
macro "xw " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := $ri hfork s
  clear s))

set_option hygiene false in
/-- A `JUMPDEST` at the walk's pc, landing at `pc'`. -/
macro "xjd " pc:term:max : tactic =>
  `(tactic| (
  replace h := xa_jumpdestAt (pc' := $pc) (atJ hcode (by kernel_rfl)) (by rfl) h
  obtain ⟨_, h⟩ := h))

set_option hygiene false in
/-- A `JUMP` to `pc'`. -/
macro "xjmp " pc:term:max : tactic =>
  `(tactic| (
  replace h := xa_jumpAt (pc' := $pc) (atJ hcode (by kernel_rfl)) (by rfl) h
  obtain ⟨_, h⟩ := h))

set_option hygiene false in
/-- A `JUMPI` falling to `pf` or jumping to `pt`, split on its condition `hw`. -/
macro "xji " pf:term:max pt:term:max hw:ident : tactic =>
  `(tactic| (
  replace h := xa_jumpiAt (pf := $pf) (pt := $pt) (atJ hcode (by kernel_rfl)) (by rfl)
    (by rfl) h
  rcases h with ⟨$hw, _, h⟩ | ⟨$hw, _, h⟩))

set_option hygiene false in
/-- The `REVERT` at the walk's pc. -/
macro "xrevert" : tactic => `(tactic| exact (xa_revert (atL hcode (by kernel_rfl)) h).elim)

set_option hygiene false in
/-- A reverting arm `PUSH1 0; DUP1; REVERT` at the walk's pc closes the goal. -/
macro "xdead" : tactic => `(tactic| (
  replace h := xa_next (n := .push [0] (by decide)) (atN hcode (by kernel_rfl)) (by nofun) h
  obtain ⟨_, _, h⟩ := h
  replace h := xa_next (n := .reg (.dup 0)) (atN hcode (by kernel_rfl)) (by nofun) h
  obtain ⟨_, _, h⟩ := h
  exact (xa_revert (atL hcode (by kernel_rfl)) h).elim))

/-- `wchain` over images that hold the `transfer` selector. -/
macro "wchainT" : tactic => `(tactic| ((try simp only [transferSel]); wchain))

theorem lockSlot_lit : Bytes.toB256 [255, 255, 255] = lockSlot := by decide
theorem tokenSlot_lit : Bytes.toB256 [5] = tokenSlot := by decide
theorem feeSlot_lit : Bytes.toB256 [0x02] = feeSlot := by decide
theorem adminFeeSlot_lit : Bytes.toB256 [0x03] = adminFeeSlot := by decide
theorem isKilledSlot_lit : Bytes.toB256 [0x0f] = isKilledSlot := by decide
theorem lock_ne_token : lockSlot ≠ tokenSlot := by decide



end Blanc.Lift.Curve3Pool
