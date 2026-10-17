import Blanc.Lift.FrameWalk
import Blanc.Lift.Curve3Pool.CheckTries
import Blanc.Lift.NodeWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Vyper
import Blanc.Lift.VyperRawCall
import Blanc.Lift.InvWalkGas

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

/-! ## Memory as a byte image

The walks carry memory as an opaque `M` with `Mem.Reads M img` and `Mem.Wf M`: reads are slices
of the image, writes lay the payload over it (`Bytes.writeAt`). -/

section Image

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat} {img : Bytes} {d : Devm}

theorem ri_mload_img {i : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ M' G', d = St b (Bytes.toB256 (img.sliceD i.toNat 32 0) :: S) M' G' ∧
      Mem.Reads M' img ∧ Mem.Wf M' := by
  obtain ⟨G', rfl⟩ := ri_mload h
  exact ⟨M.extend i.toNat 32, G', by rw [Mem.Reads.read hR]; rfl, Mem.Reads.extend hR _ _,
    Mem.Wf.extend hW _ _⟩

theorem ri_mstore_img {i v : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ M' G', d = St b S M' G' ∧ Mem.Reads M' (Bytes.writeAt img i.toNat v.toBytes) ∧
      Mem.Wf M' := by
  obtain ⟨G', rfl⟩ := ri_mstore h
  exact ⟨_, G', rfl, Mem.Reads.write hW hR _ _, Mem.Wf.write hW _ _⟩

theorem ri_calldatacopy_img {di si sz : B256} (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ M' G', d = St b S M' G' ∧
      Mem.Reads M' (Bytes.writeAt img di.toNat (sevm.data.sliceD si.toNat sz.toNat 0)) ∧
      Mem.Wf M' := by
  obtain ⟨G', rfl⟩ := ri_calldatacopy h
  exact ⟨_, G', rfl, Mem.Reads.write hW hR _ _, Mem.Wf.write hW _ _⟩

end Image

/-! ## Steps with the next pc normalized -/

section Steps

variable {post : Devm} {L : List Exec.Frame} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {d : Devm}

theorem xa_nextAt {n : Ninst} {pc' : Nat} (hat : Ninst.At sevm.code pc n)
    (hn : ∀ x, n ≠ .exec x) (hpc : pc + n.size = pc') (h : XAt sevm post pc d L) :
    ∃ d', Ninst.Run sevm d n d' ∧ XAt sevm post pc' d' L := hpc ▸ xa_next hat hn h

theorem xa_jumpdestAt {pc' : Nat} (hat : Jinst.At sevm.code pc .jumpdest) (hpc : pc + 1 = pc')
    (h : XAt sevm post pc (St b S M G) L) : ∃ G', XAt sevm post pc' (St b S M G') L :=
  hpc ▸ xa_jumpdest_St hat h

theorem xa_jumpAt {dd : B256} {pc' : Nat} (hat : Jinst.At sevm.code pc .jump)
    (hpc : dd.toNat = pc') (h : XAt sevm post pc (St b (dd :: S) M G) L) :
    ∃ G', XAt sevm post pc' (St b S M G') L :=
  hpc ▸ xa_jump_St hat h

theorem xa_jumpiAt {dd w : B256} {pf pt : Nat} (hat : Jinst.At sevm.code pc .jumpi)
    (hf : pc + 1 = pf) (ht : dd.toNat = pt) (h : XAt sevm post pc (St b (dd :: w :: S) M G) L) :
    (w = 0 ∧ ∃ G', XAt sevm post pf (St b S M G') L) ∨
      (w ≠ 0 ∧ ∃ G', XAt sevm post pt (St b S M G') L) :=
  hf ▸ ht ▸ xa_jumpi_St hat h

end Steps

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

/-! ## Branch conditions -/

theorem eqCheck_ne_zero {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
  unfold B256.eqCheck at h
  split_ifs at h with e
  · exact e
  · exact absurd rfl h

theorem eqCheck_eq_zero {x y : B256} (h : B256.eqCheck x y = 0) : x ≠ y := by
  intro e
  unfold B256.eqCheck at h
  simp only [e, ↓reduceIte] at h
  exact absurd h (by decide)

/-- `ISZERO (EQ x y)` fell through: `x = y`. -/
theorem isNe_fall {x y : B256} (h : B256.eqCheck (B256.eqCheck x y) 0 = 0) : x = y :=
  eqCheck_ne_zero (eqCheck_eq_zero h)

/-- `ISZERO (EQ x y)` jumped: `x ≠ y`. -/
theorem isNe_jump {x y : B256} (h : B256.eqCheck (B256.eqCheck x y) 0 ≠ 0) : x ≠ y :=
  eqCheck_eq_zero (eqCheck_ne_zero h)

theorem ltCheck_eq_zero_of_le {x y : B256} (h : y.toNat ≤ x.toNat) : B256.ltCheck x y = 0 := by
  unfold B256.ltCheck
  have : ¬ x < y := by rw [B256.lt_iff_toNat_lt_toNat]; omega
  simp only [this, ↓reduceIte]


end Blanc.Lift.Curve3Pool
