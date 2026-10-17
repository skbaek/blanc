import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.ReachDispatch
import Blanc.Lift.ExactWalkSolc
import Blanc.AddressSlotProofs
import Blanc.Lift.Deploy

/-!
# Cut-run walk kit for certificate-driven inversions

Contract-neutral steps for inverting a lifted run (`SFunc.RunCut … []`, i.e. `SFunc.RunP` through
`SFunc.runP_iff_runCutP_nil`) and a prefix reach (`Reach`) node by node over a checked certificate:

* terminals (`ric_stop`, `ric_return`) and internal calls into a callee that cannot halt
  (`ric_callRet`, from a `NoHaltSet`);
* a solc dispatcher's comparison rows with the branch decided by a closed comparison
  (`ric_gt_le`/`ric_gt_gt`/`ric_eq_miss`/`ric_eq_hit`, and the `rr_*` reach forms);
* storage projections of the walk bases (`afterSload`, `afterSstore`, `addLog`, `St`);
* solc's mapping hash over the scratch words (`keccak_scratch`), including the reuse of the key
  word left by the previous hash (`keccak_scratch2`, from `Mem.read_after_right_write`).
-/

namespace Blanc.Lift

open Jaune Blanc

section Kit

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

theorem ric_stop {d : Devm} (run : SFunc.RunCut fs sevm C d (.last .stop) r) :
    r = .done (.halted d) := by
  cases run with
  | last h => cases h; rfl

theorem ric_return {i sz : B256} {D : Devm}
    (run : SFunc.RunCut fs sevm C (St b (i :: sz :: S) M G) (.last .return_) (.done (.halted D))) :
    D.getStor sevm.currentTarget = b.getStor sevm.currentTarget := by
  cases run with
  | last h => exact (ri_return h).2.1 _

theorem ric_callRet {E : List Nat} {k : Nat} {dd : B256} (hE : NoHaltSet fs E = true)
    (hkE : k ∈ E) (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G' D, SFunc.Run fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunCut fs sevm C D f r := by
  obtain ⟨G', ⟨D, callee, rest⟩ | ⟨D, callee, -⟩⟩ := ric_call hk run
  · exact ⟨G', D, callee, rest⟩
  · have h := (List.all_eq_true.mp hE) k hkE
    rw [hk] at h
    simp only [Bool.and_eq_true] at h
    exact (SFunc.RunP.not_halted hE h.1 h.2 callee rfl).elim

theorem ric_gt_le {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    (h : B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0)
    (run : SFunc.RunCut fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g))))) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (sel :: S) M G') f r := by
  obtain ⟨G', run⟩ := ric_cmp_gt run
  rw [ite_eq_left h] at run
  exact ⟨G', run⟩

theorem ric_gt_gt {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    (h : B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel ≠ 0)
    (run : SFunc.RunCut fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g))))) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (sel :: S) M G') g r := by
  obtain ⟨G', run⟩ := ric_cmp_gt run
  rw [ite_eq_right h] at run
  exact ⟨G', run⟩

theorem ric_eq_miss {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {j : Nat}
    (h : B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0)
    (run : SFunc.RunCut fs sevm [] (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j))))) r) :
    ∃ G', SFunc.RunCut fs sevm [] (St b (sel :: S) M G') f r := by
  cases hj : fs[j]? with
  | none =>
    obtain ⟨_, s, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s
    obtain ⟨_, s, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s
    obtain ⟨_, s, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_eq s
    obtain ⟨_, s, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s
    cases run with
    | toZero d0 hp k => exact ⟨_, (St.of_pop2 hp).2.2 ▸ k⟩
    | toSuccCut _ _ _ hk' _ => exact absurd hk' List.not_mem_nil
    | toSucc _ _ _ _ hk' _ _ => rw [hj] at hk'; cases hk'
  | some g' =>
    obtain ⟨G', run⟩ := ric_cmp_eq (g := g') List.not_mem_nil hj run
    rw [ite_eq_left h] at run
    exact ⟨G', run⟩

theorem ric_eq_hit {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {j : Nat}
    (h : B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel ≠ 0) (lookup : fs[j]? = some g)
    (run : SFunc.RunCut fs sevm [] (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j))))) r) :
    ∃ G', SFunc.RunCut fs sevm [] (St b (sel :: S) M G') g r := by
  obtain ⟨G', run⟩ := ric_cmp_eq (List.not_mem_nil) lookup run
  rw [ite_eq_right h] at run
  exact ⟨G', run⟩

end Kit

section ReachKit

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf} {f g : SFunc}

theorem rr_gt_le (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    (h : B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0)
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g)))), K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G', f, K⟩ T := by
  obtain ⟨G', run⟩ := rr_cmp_gt hP run hT
  rw [ite_eq_left h] at run
  exact ⟨G', run⟩

theorem rr_gt_gt (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    (h : B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel ≠ 0)
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g)))), K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G', g, K⟩ T := by
  obtain ⟨G', run⟩ := rr_cmp_gt hP run hT
  rw [ite_eq_right h] at run
  exact ⟨G', run⟩

theorem rr_eq_miss (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {j : Nat} (lookup : fs[j]? = some g)
    (h : B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0)
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j)))), K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G', f, K⟩ T := by
  obtain ⟨G', run⟩ := rr_cmp_eq hP lookup run hT
  rw [ite_eq_left h] at run
  exact ⟨G', run⟩

theorem rr_eq_hit (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {j : Nat} (lookup : fs[j]? = some g)
    (h : B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel ≠ 0)
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j)))), K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G', g, K⟩ T := by
  obtain ⟨G', run⟩ := rr_cmp_eq hP lookup run hT
  rw [ite_eq_right h] at run
  exact ⟨G', run⟩

end ReachKit

theorem eq_of_eqCheck_ne_zero {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
  unfold B256.eqCheck at h
  by_contra hxy
  exact h (ite_eq_right hxy)

theorem afterSload_getStorVal (sevm : Sevm) (d : Devm) (k : B256) (a : Adr) (k' : B256) :
    (afterSload sevm d k).getStorVal a k' = d.getStorVal a k' := by
  show (Devm.getStor _ a).get k' = (Devm.getStor d a).get k'
  rw [afterSload_getStor]

theorem afterSstore_getStorVal (sevm : Sevm) (d : Devm) (k v k' : B256) :
    (afterSstore sevm d k v).getStorVal sevm.currentTarget k' =
      ((d.getStor sevm.currentTarget).set k v).get k' := by
  show (Devm.getStor _ _).get k' = _
  rw [afterSstore_getStor_self]

theorem getStorVal_eq (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.getStor a).get k := rfl

/-- The 20-byte address mask. -/
abbrev ff20 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The upper 96 bits. -/
abbrev hi96 : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The low 255 bits. -/
abbrev lo255 : B256 := Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff]

/-- solc's mapping hash over the scratch words. -/
theorem keccak_scratch (M : Mem) (x c : B256) :
    (((M.write (Bytes.toB256 [0]).toNat x.toBytes).write (Bytes.toB256 [32]).toNat c.toBytes).read
      (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).1.keccak = mapSlot x c := by
  rw [show (Bytes.toB256 [0]).toNat = 0 from by decide, show (Bytes.toB256 [32]).toNat = 32 from by decide,
    show (Bytes.toB256 [64]).toNat = 64 from by decide, scratch_read]
  rfl

/-- A 64-byte read at `0` after a word write at `32`, over a memory whose first word reads
`left`. -/
theorem Mem.read_after_right_write (μ : Mem) (left right : B256)
    (h : ∀ i < 32, μ.data.getD i 0 = left.toBytes.getD i 0) :
    ((μ.write 32 right.toBytes).read 0 64).1 = left.toBytes ++ right.toBytes := by
  have hne : right.toBytes ≠ [] := by
    intro e
    have hlen := B256.length_toBytes right
    simp only [e, List.length_nil, OfNat.zero_ne_ofNat] at hlen
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range, List.length_append,
      B256.length_toBytes, Nat.reduceAdd]
  · intro i hleft hright
    simp only [List.length_map, List.length_range] at hleft
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [Mem.getD_write_below_end _ 32 hne (by simp only [B256.length_toBytes]; omega)]
    by_cases hhalf : i < 32
    · rw [ite_eq_right (by omega), Nat.zero_add, h i hhalf]
      calc
        left.toBytes.getD i 0 = (left.toBytes ++ right.toBytes).getD i 0 :=
          (List.getD_append_left (d := (0 : UInt8))
            (by simpa only [B256.length_toBytes] using hhalf)).symm
        _ = (left.toBytes ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hright]
          rfl
    · rw [ite_eq_left (by omega), Nat.zero_add]
      calc
        right.toBytes.getD (i - 32) 0 = (left.toBytes ++ right.toBytes).getD i 0 := by
          rw [List.getD_append_right (d := (0 : UInt8))
            (by simp only [B256.length_toBytes]; omega), B256.length_toBytes]
        _ = (left.toBytes ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hright]
          rfl

/-- solc's mapping hash reusing the key word left in scratch by the previous hash. -/
theorem keccak_scratch2 (M : Mem) (x c c' : B256) :
    (((((M.write (Bytes.toB256 [0]).toNat x.toBytes).write (Bytes.toB256 [32]).toNat
      c.toBytes).read (Bytes.toB256 [0]).toNat (Bytes.toB256 [64]).toNat).2.write
      (Bytes.toB256 [32]).toNat c'.toBytes).read (Bytes.toB256 [0]).toNat
      (Bytes.toB256 [64]).toNat).1.keccak = mapSlot x c' := by
  rw [show (Bytes.toB256 [0]).toNat = 0 from by decide, show (Bytes.toB256 [32]).toNat = 32 from by decide,
    show (Bytes.toB256 [64]).toNat = 64 from by decide, Mem.read_after_right_write _ x c']
  · rfl
  · intro i hi
    have hx : x.toBytes ≠ [] := by
      intro e
      have hlen := B256.length_toBytes x
      simp only [e, List.length_nil, OfNat.zero_ne_ofNat] at hlen
    have hc : c.toBytes ≠ [] := by
      intro e
      have hlen := B256.length_toBytes c
      simp only [e, List.length_nil, OfNat.zero_ne_ofNat] at hlen
    show ((M.write 0 x.toBytes).write 32 c.toBytes).data.getD i 0 = _
    rw [Mem.getD_write_below_end _ 32 hc (by simp only [B256.length_toBytes]; omega),
      ite_eq_right (by omega), Mem.getD_write_below_end _ 0 hx (by simp only [B256.length_toBytes]; omega),
      ite_eq_left (by omega), Nat.sub_zero]


end Blanc.Lift
