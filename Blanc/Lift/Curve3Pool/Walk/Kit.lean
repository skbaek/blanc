import Blanc.Lift.FrameWalk
import Blanc.Lift.Curve3Pool.CheckTries
import Blanc.Lift.NodeWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.Vyper
import Blanc.Lift.VyperRawCall
import Blanc.Lift.InvWalkGas
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

theorem ri_mload_imgAt {i : B256} {o : Nat} (ho : i.toNat = o) (hR : Mem.Reads M img)
    (hW : Mem.Wf M) (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ M' G', d = St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M' G' ∧
      Mem.Reads M' img ∧ Mem.Wf M' := ho ▸ ri_mload_img hR hW h

theorem ri_mstore_imgAt {i v : B256} {o : Nat} (ho : i.toNat = o) (hR : Mem.Reads M img)
    (hW : Mem.Wf M) (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ M' G', d = St b S M' G' ∧ Mem.Reads M' (Bytes.writeAt img o v.toBytes) ∧
      Mem.Wf M' := ho ▸ ri_mstore_img hR hW h

theorem ri_calldatacopy_imgAt {di si sz : B256} {o z : Nat} (ho : di.toNat = o) (hz : sz.toNat = z)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (di :: si :: sz :: S) M G) (.reg .calldatacopy) d) :
    ∃ M' G', d = St b S M' G' ∧
      Mem.Reads M' (Bytes.writeAt img o (sevm.data.sliceD si.toNat z 0)) ∧ Mem.Wf M' :=
  ho ▸ hz ▸ ri_calldatacopy_img hR hW h

theorem ri_keccak_imgAt {i sz : B256} {o z : Nat} (ho : i.toNat = o) (hz : sz.toNat = z)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : Ninst.Run sevm (St b (i :: sz :: S) M G) (.reg .keccak256) d) :
    ∃ M' G', d = St b (Bytes.keccak (img.sliceD o z 0) :: S) M' G' ∧ Mem.Reads M' img ∧ Mem.Wf M' := by
  subst ho hz
  obtain ⟨G', rfl⟩ := ri_keccak h
  exact ⟨M.extend i.toNat sz.toNat, G', by rw [Mem.Reads.read hR]; rfl, Mem.Reads.extend hR _ _,
    Mem.Wf.extend hW _ _⟩

end Image

/-! ## A `STATICCALL` over the image carrier -/

section StaticImg

variable {post : Devm} {L : List Exec.Frame} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {img : Bytes}

/-- **A `STATICCALL` step over the image carrier**: the flag and returned data `out`, the output
window written into the image, storage and logs kept; on a nonzero flag, either a precompile
target and no child, or the next remaining child is the call's (at `t`, with the input window as
calldata, static, returning `out`, logging nothing). -/
theorem xa_staticcall_img {pc' : Nat} {g t ii is oi os : B256} {i n o z : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: t :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag out M' L', XAt sevm post pc' (St d (flag :: S) M' d.gasLeft) L' ∧
      Mem.Reads M' (Bytes.writeAt img o (out.take z)) ∧ Mem.Wf M' ∧
      d.returnData = out ∧ out.length < 2 ^ 256 ∧ (∀ a, d.getStor a = b.getStor a) ∧
      d.logs = b.logs ∧
      (flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ d.output = b.output ∧ Devm.AccGrow b d ∧
          (∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a) ∧
          c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = img.sliceD i n 0 ∧
          c.sevm.isStatic = true ∧ c.post.output = out ∧ c.post.logs = [] ∧
          (∀ a, c.pre.getCode a = b.getCode a) ∧ (∀ a, d.getCode a = c.post.getCode a))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_staticcall hfork hat rfl h
  obtain ⟨flag, out, hpost, hbound, -⟩ := ri_staticcall_bounded hfork s
  refine ⟨d, flag, out, _, L', hpost.eq_St ▸ h, Mem.Reads.write (Mem.Wf.extends _ hW)
    (Mem.Reads.extends _ hR) _ _, Mem.Wf.write (Mem.Wf.extends _ hW) _ _, hpost.returnData,
    hbound, hpost.stor, hpost.logs, fun nz => ?_⟩
  rcases hk flag S hpost.stack nz with hp | ⟨c, hL, -, -, hc⟩
  · exact .inl hp
  · refine .inr ⟨c, hL, hc.outputKeep, hc.warm, hc.code, hc.target, ?_, hc.isStatic,
      hc.output.trans hpost.returnData, ?_, hc.codePre, hc.codePost⟩
    · rw [hc.data]
      exact Mem.Reads.read hR _ _
    · have e := hc.logs
      rw [hpost.logs] at e
      have e2 : b.logs ++ c.post.logs = b.logs := e.symm
      exact List.append_right_eq_self.mp e2

/-- **An identity-precompile copy** (`CALL(gas, 4, 0, ii, is, oi, os)`) over the image carrier:
it pushed `0`, or it pushed `1`, spawned no child, kept the world (`ShaCallPost`) and laid the
input window (truncated to `os`) over the output window. -/
theorem xa_identity_img {pc' : Nat} {g ii is oi os : B256} {i n o z : Nat}
    (hid : IdReady sevm b) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d L', XAt sevm post pc' d L' ∧
      (d.stack = 0 :: S ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M')) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_call hid.fork hat rfl h
  refine ⟨d, L', h, ?_⟩
  rcases ri_call_identity hid s with h0 | ⟨b', G', hpost, rfl⟩
  · exact .inl h0
  · refine .inr ⟨?_, b', G', _, ?_, rfl, ?_, ?_⟩
    · rcases hk 1 S rfl (by decide) with ⟨-, hL⟩ | ⟨c, -, -, hfr, -⟩
      · exact hL
      · exfalso
        rcases hfr with hp | hdel
        · exact hp (of_decide_eq_true hid.pre)
        · have e : getDelegatedCodeAddress
              ((St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G).getCode (4 : B256).toAdr) =
              none := by
            rw [show (4 : B256).toAdr = (4 : Adr) by decide]
            exact hid.nodeleg
          rw [e] at hdel
          exact absurd hdel (by decide)
    · rw [← Mem.Reads.read hR]
      exact hpost
    · rw [← Mem.Reads.read hR]
      exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
    · exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _

/-- **A `CALL` over the image carrier**: the flag on the stack over the resumed machine `d` (its
own base); on a nonzero flag, the output window holds (a prefix of) the returned data, and either
the target is a precompile and no child was spawned, or the next remaining child is the call's
(`ChildOf`, with the input window as calldata) and it ran a code frame. -/
theorem xa_call_img {pc' : Nat} {g t v ii is oi os : B256} {i n o z : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag L', XAt sevm post pc' (St d (flag :: S) d.memory d.gasLeft) L' ∧
      (flag ≠ 0 →
        Mem.Reads d.memory (Bytes.writeAt img o (d.returnData.take z)) ∧ Mem.Wf d.memory ∧
        d.output = b.output ∧
        ((sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
          (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧
            (¬ sevm.benvStat.rules.isPrecomp t.toAdr ∨
              (getDelegatedCodeAddress (b.getCode t.toAdr)).isSome) ∧
            ChildOf (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) d t.toAdr
              (img.sliceD i n 0) v sevm.isStatic c))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_call hfork hat rfl h
  obtain ⟨flag, hpost⟩ := ri_call_post hfork s
  rw [St.self hpost.stack rfl] at h
  refine ⟨d, flag, L', h, fun nz => ?_⟩
  obtain ⟨hmem, hout⟩ := hpost.settled nz
  refine ⟨?_, ?_, hout, ?_⟩
  · rw [hmem]
    exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
  · rw [hmem]
    exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _
  · rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, hfr, hc⟩
    · exact .inl hp
    · refine .inr ⟨c, hL, hdep, hfr, ?_⟩
      rw [St.memory, Mem.Reads.read hR] at hc
      exact hc

end StaticImg

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

/-! ## Words of a byte image -/

/-- The image's 32-byte word at `o` is `w`. -/
def WordAt (img : Bytes) (o : Nat) (w : B256) : Prop := img.sliceD o 32 0 = w.toBytes

namespace WordAt

variable {img : Bytes} {o n : Nat} {w : B256} {xs : Bytes}

theorem read (h : WordAt img o w) : Bytes.toB256 (img.sliceD o 32 0) = w := by
  rw [h]
  exact B256.toB256_toBytes w

theorem write_self (img : Bytes) (o : Nat) (w : B256) :
    WordAt (Bytes.writeAt img o w.toBytes) o w := by
  unfold WordAt
  rw [show (32 : Nat) = w.toBytes.length from (B256.length_toBytes w).symm, Bytes.sliceD_writeAt]

theorem write_other (h : WordAt img o w) (hd : o + 32 ≤ n ∨ n + xs.length ≤ o) :
    WordAt (Bytes.writeAt img n xs) o w := by
  unfold WordAt at h ⊢
  rcases hd with hd | hd
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hd, h]
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ hd, h]

end WordAt

/-! ## Storage reads through the walk's bases -/

theorem getStorVal_eq (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.getStor a).get k :=
  rfl

theorem getStorVal_afterSload {sevm : Sevm} {b : Devm} {k : B256} (a : Adr) (x : B256) :
    (afterSload sevm b k).getStorVal a x = b.getStorVal a x := by
  rw [getStorVal_eq, afterSload_getStor]
  rfl

theorem getStorVal_afterSstore_self {sevm : Sevm} {b : Devm} {k v : B256} (x : B256) :
    (afterSstore sevm b k v).getStorVal sevm.currentTarget x =
      ((b.getStor sevm.currentTarget).set k v).get x := by
  rw [getStorVal_eq, afterSstore_getStor_self]

theorem getStorVal_afterSstore_ne {sevm : Sevm} {b : Devm} {k v x : B256} (h : k ≠ x) :
    (afterSstore sevm b k v).getStorVal sevm.currentTarget x = b.getStorVal sevm.currentTarget x := by
  rw [getStorVal_afterSstore_self, Stor.get_set_ne _ h]
  rfl

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

theorem gtCheck_ne_zero {x y : B256} (h : B256.gtCheck x y ≠ 0) : y < x := by
  unfold B256.gtCheck at h
  split_ifs at h with e
  · exact e
  · exact absurd rfl h

theorem ltCheck_eq_zero_of_le {x y : B256} (h : y.toNat ≤ x.toNat) : B256.ltCheck x y = 0 := by
  unfold B256.ltCheck
  have : ¬ x < y := by rw [B256.lt_iff_toNat_lt_toNat]; omega
  simp only [this, ↓reduceIte]


/-! ## Byte-image helpers -/


theorem List.sliceD_length_eq {xs : List UInt8} {n : Nat} :
    xs.sliceD xs.length n 0 = List.replicate n 0 := by
  rw [List.sliceD_eq_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_replicate]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ xs.length + k),
      Option.getD_none]

theorem List.sliceD_zero_of_length {xs : List UInt8} {n : Nat} (h : xs.length = n) :
    xs.sliceD 0 n 0 = xs := by
  rw [List.sliceD_eq_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, h]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

theorem List.sliceD_replicate_zero {k m n : Nat} :
    (List.replicate k (0 : UInt8)).sliceD m n 0 = List.replicate n 0 := by
  rw [List.sliceD_eq_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_replicate]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate,
      List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

theorem zero_lit : Bytes.toB256 [0] = 0 := by decide

theorem lockSlot_lit : Bytes.toB256 [255, 255, 255] = lockSlot := by decide
theorem tokenSlot_lit : Bytes.toB256 [5] = tokenSlot := by decide
theorem lock_ne_token : lockSlot ≠ tokenSlot := by decide



end Blanc.Lift.Curve3Pool
