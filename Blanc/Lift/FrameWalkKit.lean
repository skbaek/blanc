import Blanc.Lift.FrameWalk
import Blanc.Lift.NodeWalk
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkGas
import Blanc.Lift.IdentityCallGas
import Blanc.Lift.ReturnDataBound
import Blanc.Lift.InvWalkStep
import Blanc.Lift.WalkCutKit
import Jaune.WordFacts

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
* branch conditions (`isNe_fall`, `or_ne_zero`, …; the plain flag facts are Jaune's
  `B256.eq_of_eqCheck_ne_zero`, `B256.lt_of_gtCheck_ne_zero`, `B256.not_lt_of_ltCheck_eq_zero`), Vyper's checked product `mul_check_toNat`, and `ChildOf.congr_left`.

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
    (hid : IdReady sevm b) (hcov : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d L', XAt sevm post pc' d L' ∧
      ((d.stack = 0 :: S ∧ (g = Nat.toB256 G → 0 < sevm.depth → n ≤ 32 → d.gasLeft = 0)) ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M')) := by
  subst hpc hii his hoi hos
  have hG : G < 2 ^ 256 := h.gasLeft_lt
  obtain ⟨d, s, L', h, hk⟩ := xa_call hcov hat rfl h
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

end Steps

/-! ## Words of a byte image -/

/-- The image's 32-byte word at `o` is `w`. -/
def WordAt (img : Bytes) (o : Nat) (w : B256) : Prop := img.sliceD o 32 0 = w.toBytes

namespace WordAt

variable {img : Bytes} {o n : Nat} {w : B256} {xs : Bytes}

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

end Region

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

theorem getStorVal_afterSstore_self {sevm : Sevm} {b : Devm} {k v : B256} (x : B256) :
    (afterSstore sevm b k v).getStorVal sevm.currentTarget x =
      ((b.getStor sevm.currentTarget).set k v).get x := by
  rw [getStorVal_eq, afterSstore_getStor_self]

/-! ## Branch conditions -/


/-! ## Byte-image helpers -/











end Blanc.Lift
