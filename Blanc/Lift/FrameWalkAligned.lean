import Blanc.Lift.FrameWalkKit
import Blanc.Lift.VyperCallee

/-!
# Word-aligned memory along a frame walk

The image carrier of `FrameWalkKit.lean` (`Mem.Reads M img`, `Mem.Wf M`) forgets the memory's
logical size. Internal calls whose contracts track memory words (`MemTrack`, the frame saves of
Vyper callees) need it word-aligned: `M.size % 32 = 0`. Every EVM memory step keeps an aligned
size aligned (an expansion rounds up to a word, a write grows to `ceil32`); this module states
that for the image-carrier steps:

* `Mem.size_write_mod32`, `Mem.size_extends_mod32`;
* `ri_mload_imgAtA`, `ri_mstore_imgAtA`, `ri_calldatacopy_imgAtA`, `ri_keccak_imgAtA`: the
  `ri_*_imgAt` steps with the size kept aligned;
* `xa_staticcall_imgA`, `xa_call_imgA`, `xa_identity_imgA`: the spawning steps, likewise.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A write keeps an aligned logical size aligned. -/
theorem Mem.size_write_mod32 {μ : Mem} {n : Nat} {xs : Bytes} (h : μ.size % 32 = 0) :
    (μ.write n xs).size % 32 = 0 := by
  match xs with
  | [] => exact h
  | x :: xs' =>
    simp only [Mem.write]
    split_ifs
    · exact h
    · exact h
    · show ceil32 _ % 32 = 0
      unfold ceil32; split <;> omega

/-- An expansion over several windows keeps an aligned logical size aligned. -/
theorem Mem.size_extends_mod32 {μ : Mem} (ps : List (Nat × Nat)) (h : μ.size % 32 = 0) :
    (μ.extends ps).size % 32 = 0 := by
  show memExtsSize μ.size ps % 32 = 0
  induction ps generalizing μ with
  | nil => exact h
  | cons p ps ih =>
    exact ih (μ := μ.extend p.1 p.2) (Mem.size_extend_mod p.1 p.2 h)

variable {sevm : Sevm} {pc : Nat} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {img : Bytes}
  {d : Devm}

variable {post : Devm} {L : List Exec.Frame}

/-- `xa_staticcall_img` with the memory kept aligned. -/
theorem xa_staticcall_imgA {pc' : Nat} {g t ii is oi os : B256} {i n o z : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: t :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag out M' L', XAt sevm post pc' (St d (flag :: S) M' d.gasLeft) L' ∧
      (∃ d₀, Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall)
        d₀ ∧ d₀.getCode = d.getCode) ∧
      Mem.Reads M' (Bytes.writeAt img o (out.take z)) ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
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
    (Mem.Reads.extends _ hR) _ _, Mem.Wf.write (Mem.Wf.extends _ hW) _ _,
    Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA), hpost.returnData,
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

/-- `xa_call_img` with the memory kept aligned on a nonzero flag. -/
theorem xa_call_imgA {pc' : Nat} {g t v ii is oi os : B256} {i n o z : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag L', XAt sevm post pc' (St d (flag :: S) d.memory d.gasLeft) L' ∧
      Ninst.Run sevm (St b (g :: t :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      d.returnData.length < 2 ^ 256 ∧ (flag ≠ 0 →
        Mem.Reads d.memory (Bytes.writeAt img o (d.returnData.take z)) ∧ Mem.Wf d.memory ∧
        d.memory.size % 32 = 0 ∧ d.output = b.output ∧
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
  refine ⟨?_, ?_, ?_, hout, ?_⟩
  · rw [hmem]
    exact Mem.Reads.write (Mem.Wf.extends _ hW) (Mem.Reads.extends _ hR) _ _
  · rw [hmem]
    exact Mem.Wf.write (Mem.Wf.extends _ hW) _ _
  · rw [hmem]
    exact Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA)
  · rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, hfr, hc⟩
    · exact .inl hp
    · refine .inr ⟨c, hL, hdep, hfr, ?_⟩
      rw [St.memory, Mem.Reads.read hR] at hc
      exact hc

/-- `xa_identity_img` with the memory kept aligned. -/
theorem xa_identity_imgA {pc' : Nat} {g ii is oi os : B256} {i n o z : Nat}
    (hid : IdReady sevm b) (hcov : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .call))
    (hpc : pc + 1 = pc') (hii : ii.toNat = i) (his : is.toNat = n) (hoi : oi.toNat = o)
    (hos : os.toNat = z) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hA : M.size % 32 = 0)
    (h : XAt sevm post pc (St b (g :: 4 :: 0 :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d L', XAt sevm post pc' d L' ∧
      ((d.stack = 0 :: S ∧ (g = Nat.toB256 G → 0 < sevm.depth → n ≤ 32 → d.gasLeft = 0)) ∨
        (L = L' ∧ ∃ b' G' M', ShaCallPost b b' (img.sliceD i n 0) ∧ d = St b' (1 :: S) M' G' ∧
          Mem.Reads M' (Bytes.writeAt img o ((img.sliceD i n 0).take z)) ∧ Mem.Wf M' ∧
          M'.size % 32 = 0)) := by
  subst hpc hii his hoi hos
  have hG : G < 2 ^ 256 := h.gasLeft_lt
  obtain ⟨d, s, L', h, hk⟩ := xa_call hcov hat rfl h
  refine ⟨d, L', h, ?_⟩
  rcases ri_call_identity hid s with h0 | ⟨b', G', hpost, rfl⟩
  · refine .inl ⟨h0, fun hg hdep hn => ?_⟩
    subst hg
    exact ri_call_identity_gas_fail hid hdep hG hn s h0
  · refine .inr ⟨?_, b', G', _, ?_, rfl, ?_, ?_, ?_⟩
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
    · exact Mem.size_write_mod32 (Mem.size_extends_mod32 _ hA)

end Blanc.Lift
