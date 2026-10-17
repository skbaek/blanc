import Blanc.Lift.FrameWalk
import Blanc.Lift.NodeWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkGas
import Blanc.Lift.IdentityCallGas
import Blanc.Lift.ReturnDataBound

/-!
# Walking an actual frame derivation over a memory image

Companions to `Blanc/Lift/FrameWalk.lean` (`XAt`) that no walk needs to restate:

* the memory carrier: an opaque `M` with `Mem.Reads M img` and `Mem.Wf M`; `ri_*_img` /
  `ri_*_imgAt` invert `MLOAD`/`MSTORE`/`CALLDATACOPY`/`SHA3` against the image;
* spawning steps over the image: `xa_staticcall_img`, `xa_call_img` (with the return-data
  bound), `xa_identity_img` (an unchecked identity copy that forwarded all gas either succeeded
  or left no gas, `ri_call_identity_gas_fail`);
* pc-normalized steps `xa_nextAt`, `xa_jumpdestAt`, `xa_jumpAt`, `xa_jumpiAt`, `XAt.of_eq`;
* image facts: `WordAt img o w` (a 32-byte word) and `Region img o xs` (any bytes), with
  `write_self`/`write_other`, `Region.append`/`left`/`right`/`head`/`copy`/`slice`, the
  `Mem.Reads.forget` cut (forget an image's construction after drawing the facts a walk still
  needs) and the `wchain` tactic (peel disjoint writes off a `WordAt`/`Region` goal);
* branch conditions (`eqCheck_ne_zero_eq`, `isNe_fall`, `gtCheck_ne_zero`, `ltCheck_eq_zero_not_lt`,
  `or_ne_zero`, …), Vyper's checked product `mul_check_toNat`, and `ChildOf.congr_left`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

variable {sevm : Sevm} {pc : Nat}

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
      (∃ d₀, Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall)
        d₀ ∧ d₀.getCode = d.getCode) ∧
      Mem.Reads M' (Bytes.writeAt img o (out.take z)) ∧ Mem.Wf M' ∧
      d.returnData = out ∧ out.length < 2 ^ 256 ∧ (∀ a, d.getStor a = b.getStor a) ∧
      d.logs = b.logs ∧
      (flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧ d.output = b.output ∧ Devm.AccGrow b d ∧
          (∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a) ∧
          c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = img.sliceD i n 0 ∧
          c.sevm.isStatic = true ∧ c.post.output = out ∧ c.post.logs = [] ∧
          (∀ a, c.pre.getCode a = b.getCode a) ∧ (∀ a, d.getCode a = c.post.getCode a))) := by
  subst hpc hii his hoi hos
  obtain ⟨d, s, L', h, hk⟩ := xa_staticcall hfork hat rfl h
  obtain ⟨flag, out, hpost, hbound, -⟩ := ri_staticcall_bounded hfork s
  refine ⟨d, flag, out, _, L', hpost.eq_St ▸ h, ⟨d, s, rfl⟩, Mem.Reads.write (Mem.Wf.extends _ hW)
    (Mem.Reads.extends _ hR) _ _, Mem.Wf.write (Mem.Wf.extends _ hW) _ _, hpost.returnData,
    hbound, hpost.stor, hpost.logs, fun nz => ?_⟩
  rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, -, hc⟩
  · exact .inl hp
  · refine .inr ⟨c, hL, hdep, hc.outputKeep, hc.warm, hc.code, hc.target, ?_, hc.isStatic,
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
      ((d.stack = 0 :: S ∧ (g = Nat.toB256 G → 0 < sevm.depth → n ≤ 32 → d.gasLeft = 0)) ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M')) := by
  subst hpc hii his hoi hos
  have hG : G < 2 ^ 256 := h.gasLeft_lt
  obtain ⟨d, s, L', h, hk⟩ := xa_call hid.fork hat rfl h
  refine ⟨d, L', h, ?_⟩
  rcases ri_call_identity hid s with h0 | ⟨b', G', hpost, rfl⟩
  · refine .inl ⟨h0, fun hg hdep hn => ?_⟩
    subst hg
    exact ri_call_identity_gas_fail hid hdep hG hn s h0
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
      Ninst.Run sevm (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      d.returnData.length < 2 ^ 256 ∧ (flag ≠ 0 →
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
  have hrd := ReturnDataBound.call_returnData_length_lt s hfork
  rw [St.self hpost.stack rfl] at h
  refine ⟨d, flag, L', h, s, hrd, fun nz => ?_⟩
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

/-- The image's bytes at `o` are `xs`. -/
def Region (img : Bytes) (o : Nat) (xs : Bytes) : Prop := img.sliceD o xs.length 0 = xs

namespace Region

variable {img : Bytes} {o n : Nat} {xs ys : Bytes} {w : B256}

theorem write_self (img : Bytes) (o : Nat) (xs : Bytes) : Region (Bytes.writeAt img o xs) o xs :=
  Bytes.sliceD_writeAt _ _ _

theorem write_other (h : Region img o xs) (hd : o + xs.length ≤ n ∨ n + ys.length ≤ o) :
    Region (Bytes.writeAt img n ys) o xs := by
  unfold Region at h ⊢
  rcases hd with hd | hd
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hd, h]
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ hd, h]

theorem of_word (h : WordAt img o w) : Region img o w.toBytes := by
  unfold Region; rw [B256.length_toBytes]; exact h

theorem word (h : Region img o w.toBytes) : WordAt img o w := by
  unfold Region at h; rw [B256.length_toBytes] at h; exact h

theorem append (h1 : Region img o xs) (h2 : Region img (o + xs.length) ys) :
    Region img o (xs ++ ys) := by
  unfold Region at h1 h2 ⊢
  rw [List.length_append, List.sliceD_split, h1, h2]

theorem left (h : Region img o (xs ++ ys)) : Region img o xs := by
  unfold Region at h ⊢
  rw [List.length_append, List.sliceD_split] at h
  exact (List.append_inj h (by rw [List.length_sliceD])).1

theorem right (h : Region img o (xs ++ ys)) : Region img (o + xs.length) ys := by
  unfold Region at h ⊢
  rw [List.length_append, List.sliceD_split] at h
  exact (List.append_inj h (by rw [List.length_sliceD])).2

/-- An identity copy of exactly the region's bytes copies them. -/
theorem copy {i z : Nat} (h : Region img i xs) (hn : n = xs.length) (hz : z = xs.length) :
    (img.sliceD i n 0).take z = xs := by
  unfold Region at h
  rw [hn, hz, h, List.take_length]

theorem read (h : Region img o xs) (hl : xs.length = 32) :
    Bytes.toB256 (img.sliceD o 32 0) = Bytes.toB256 xs := by
  unfold Region at h; rw [← hl, h]

/-- A region's bytes are the head of any longer read at its start. -/
theorem head {m : Nat} (h : Region img o xs) (hm : xs.length ≤ m) :
    (img.sliceD o m 0).take xs.length = xs := by
  unfold Region at h
  rw [show m = xs.length + (m - xs.length) by omega, List.sliceD_split, h,
    List.take_left' rfl]

end Region

/-- The first `n` bytes of a word. -/
theorem WordAt.prefix {img : Bytes} {o n : Nat} {w : B256} (h : WordAt img o w) (hn : n ≤ 32) :
    img.sliceD o n 0 = w.toBytes.take n := by
  unfold WordAt at h
  rw [← h, show (32 : Nat) = n + (32 - n) by omega, List.sliceD_split,
    List.take_left' (List.length_sliceD _ _ _ _)]

/-- Forget an image's construction, keeping only the facts drawn from it first. -/
theorem Mem.Reads.forget {M : Mem} {img : Bytes} (h : Mem.Reads M img) :
    ∃ img', Mem.Reads M img' ∧ img' = img :=
  ⟨img, h, rfl⟩

/-- Peel an image's writes off a `WordAt`/`Region` goal: a write at the goal's offset settles
it, a disjoint one is skipped. -/
macro "wchain" : tactic => `(tactic| repeat (first
  | refine WordAt.write_other ?_ (by
      simp only [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons,
        List.length_nil, List.length_append]
      omega)
  | refine Region.write_other ?_ (by
      simp only [B256.length_toBytes, List.length_take, List.length_sliceD, List.length_cons,
        List.length_nil, List.length_append]
      omega)
  | exact WordAt.write_self _ _ _
  | exact Region.write_self _ _ _))

/-! ## Storage reads through the walk's bases -/

theorem getStorVal_eq (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.getStor a).get k :=
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

theorem eqCheck_ne_zero_eq {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
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
  eqCheck_ne_zero_eq (eqCheck_eq_zero h)

/-- `ISZERO (EQ x y)` jumped: `x ≠ y`. -/
theorem isNe_jump {x y : B256} (h : B256.eqCheck (B256.eqCheck x y) 0 ≠ 0) : x ≠ y :=
  eqCheck_eq_zero (eqCheck_ne_zero_eq h)

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


theorem Region.append' {img : Bytes} {o o' : Nat} {xs ys : Bytes} (h1 : Region img o xs)
    (h2 : Region img o' ys) (ho : o' = o + xs.length) : Region img o (xs ++ ys) := by
  subst ho; exact h1.append h2


theorem Region.slice {img : Bytes} {o n : Nat} {xs : Bytes} (h : Region img o xs)
    (hn : n = xs.length) : img.sliceD o n 0 = xs := hn ▸ h


theorem gtCheck_eq_zero {x y : B256} (h : B256.gtCheck x y = 0) : ¬ y < x := by
  intro e
  unfold B256.gtCheck at h
  simp only [e, ↓reduceIte] at h
  exact absurd h (by decide)


theorem ltCheck_ne_zero_of_lt {x y : B256} (h : x < y) : B256.ltCheck x y ≠ 0 := by
  unfold B256.ltCheck
  simp only [h, ↓reduceIte]
  decide


theorem or_ne_zero {x y : B256} (h : (x ||| y) ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  by_cases hx : x = 0
  · right; intro hy; apply h; rw [hx, hy]; decide
  · exact .inl hx

theorem ltCheck_eq_zero_not_lt {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x < y := by
  intro e
  unfold B256.ltCheck at h
  simp only [e, ↓reduceIte] at h
  exact absurd h (by decide)


/-- A child's relation to its parent's state depends only on the state's code, storage, logs,
output and warm accounts. -/
theorem _root_.Blanc.Lift.ChildOf.congr_left {d e d' : Devm} {t : Adr} {input : Bytes} {v : B256} {st : Bool}
    {c : Exec.Frame} (h : ChildOf d d' t input v st c) (hc : ∀ a, d.getCode a = e.getCode a)
    (hs : ∀ a, d.getStor a = e.getStor a) (hl : d.logs = e.logs) (ho : d.output = e.output)
    (hw : d.accessedAddresses = e.accessedAddresses) : ChildOf e d' t input v st c where
  target := h.target
  data := h.data
  value := h.value
  isStatic := h.isStatic
  output := h.output
  logs := by rw [h.logs, hl]
  storPre ca hca := by rw [h.storPre ca (by rw [hc]; exact hca), hs]
  storPost ca hca := h.storPost ca (by rw [hc]; exact hca)
  code ca hca := by rw [h.code ca (by rw [hc]; exact hca), hc]
  codePre a := by rw [h.codePre, hc]
  codePost := h.codePost
  outputKeep := by rw [h.outputKeep, ho]
  warm a ha := h.warm a (by rw [hw]; exact ha)


/-- Vyper's checked product (`x * y / x == y or x == 0`) did not wrap. -/
theorem mul_check_toNat {x y : B256} (h : x * y / x = y ∨ x = 0) :
    x.toNat * y.toNat < 2 ^ 256 := by
  rcases h with h | h
  · by_cases hx : x = 0
    · rw [hx, show (0 : B256).toNat = 0 from rfl, Nat.zero_mul]; exact Nat.two_pow_pos _
    · have e := congrArg B256.toNat h
      rw [B256.toNat_div hx, B256.toNat_mul] at e
      unfold Nat.lo at e
      have hq := Nat.div_mul_le_self (x.toNat * y.toNat % 2 ^ 256) x.toNat
      rw [e] at hq
      have hm := Nat.mod_le (x.toNat * y.toNat) (2 ^ 256)
      have hl := Nat.mod_lt (x.toNat * y.toNat) (Nat.two_pow_pos 256)
      have : x.toNat * y.toNat % 2 ^ 256 = x.toNat * y.toNat := by
        apply Nat.le_antisymm hm
        rw [Nat.mul_comm] at hq; exact hq
      omega
  · rw [h, show (0 : B256).toNat = 0 from rfl, Nat.zero_mul]; exact Nat.two_pow_pos _


/-- An unwrapped checked quotient's number. -/
theorem rlOut_toNat {B A T : B256} (hm : B.toNat * A.toNat < 2 ^ 256) (hT : T ≠ 0) :
    (B * A / T).toNat = B.toNat * A.toNat / T.toNat := by
  rw [B256.toNat_div hT, B256.toNat_mul]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hm]

theorem toNat_ne_zero {T : B256} (hT : T ≠ 0) : T.toNat ≠ 0 := fun h =>
  hT (B256.toNat_inj _ _ (by rw [h]; rfl))

theorem toNat_le_of_not_lt {x y : B256} (h : ¬ x < y) : y.toNat ≤ x.toNat := by
  rw [B256.lt_iff_toNat_lt_toNat] at h; omega

/-- `XAt` over equal states. -/
theorem XAt.of_eq {sevm : Sevm} {post : Devm} {pc : Nat} {d d' : Devm} {L : List Exec.Frame}
    (e : d = d') (h : XAt sevm post pc d L) : XAt sevm post pc d' L := e ▸ h


theorem zero_lit : Bytes.toB256 [0] = 0 := by decide

/-! ## Calls that keep the caller's storage -/

/-- **Every `CALL` from the frame to `t` keeps the frame's own storage and address 4's code**: a
per-target, step-level form of "the callee makes no state-changing callback". -/
def CallKeeps (sevm : Sevm) (t : B256) : Prop :=
  ∀ (X d : Devm) (g v ii is oi os : B256) (S : List B256),
    X.stack = g :: t :: v :: ii :: is :: oi :: os :: S → Ninst.Run sevm X (.exec .call) d →
      d.getStor sevm.currentTarget = X.getStor sevm.currentTarget ∧ d.getCode 4 = X.getCode 4

/-- **Every `STATICCALL` from the frame to `t` keeps address 4's code.** -/
def StaticKeeps (sevm : Sevm) (t : B256) : Prop :=
  ∀ (X d : Devm) (g ii is oi os : B256) (S : List B256),
    X.stack = g :: t :: ii :: is :: oi :: os :: S → Ninst.Run sevm X (.exec .staticcall) d →
      d.getCode 4 = X.getCode 4

/-- A child of a call that kept the caller's storage and address 4's code left both as it found
them. -/
theorem ChildOf.keeps {sevm : Sevm} {X d : Devm} {t : Adr} {input : Bytes} {v : B256} {st : Bool}
    {c : Exec.Frame} (h : ChildOf X d t input v st c) (hX : X.getCode sevm.currentTarget ≠ .empty)
    (hs : d.getStor sevm.currentTarget = X.getStor sevm.currentTarget)
    (h4 : d.getCode 4 = X.getCode 4) :
    (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
      c.post.getCode 4 = c.pre.getCode 4 := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [← h.storPost _ hX x, hs, h.storPre _ hX]
  · rw [← h.codePost, h4, h.codePre]

end Blanc.Lift
