import Blanc.Lift.BeaconDeposit.Creation.Walk
import Blanc.Lift.HistPackedShaSize

/-! The actual constructor program under Muir Glacier: flat storage/access pricing,
no delegation, and 31 symbolic SHA-256 calls. The modern theorem is unchanged. -/

namespace Blanc.Lift.BeaconDeposit.Creation.Historical

open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit

/-- The state at the loop head before iteration `i`, apart from the stack and gas. -/
structure LoopInv (sevm : Sevm) (initial : Devm) (i : Nat) (b : Devm) (M : Mem) : Prop where
  stor : CtorStor i (Devm.getStor b sevm.currentTarget)
  error : b.error = none
  wf : Mem.Wf M
  img : ∃ img, Mem.Reads M img ∧ img.sliceD 64 32 0 = (Nat.toB256 (fp i)).toBytes
  size : M.size = memAt i
  metadata : ∀ deletions, CreateRunMeta sevm.currentTarget deletions initial →
    CreateRunMeta sevm.currentTarget deletions b

/-! ## One iteration -/

/-- The exact cost of iteration `i` from the world `b`. -/
def iterCost (sevm : Sevm) (b : Devm) (i : Nat) : Nat :=
  17 + sstoreCostH sevm (afterSloadH sevm (afterSloadH sevm b (Nat.toB256 (33 + i)))
      (Nat.toB256 (33 + i))) (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)) + 44 +
    (1336 + (calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i))) +
    sloadCostH sevm (afterSloadH sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)) + 4 + 28 +
    sloadCostH sevm b (Nat.toB256 (33 + i)) + 4 + 57

/-- **One zero-hash iteration** `i < 31`: from the loop head with `i` on the stack to the
back-edge into entry 2 with `i + 1`, storing `zeroHash sha256 (i + 1)` at slot `34 + i`. -/
theorem iter {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false) {i : Nat} (hi : i < 31) {initial b : Devm} {M : Mem}
    (inv : LoopInv sevm initial i b M) {G : Nat} (hGlo : 2300 ≤ G) (hGb : G < 2 ^ 64) :
    ∃ b' M', LoopInv sevm initial (i + 1) b' M' ∧
      SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 i] M (G + iterCost sevm b i))
        t_0014_c2 (.at 2 (St b' [Nat.toB256 (i + 1)] M' G)) := by
  rw [show G + iterCost sevm b i = G + 17 + sstoreCostH sevm (afterSloadH sevm
      (afterSloadH sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i))) (Nat.toB256 (34 + i))
      (zeroHash Bytes.sha256 (i + 1)) + 44 +
      (1336 + (calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i))) +
      sloadCostH sevm (afterSloadH sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)) + 4 + 28 +
      sloadCostH sevm b (Nat.toB256 (33 + i)) + 4 + 57 by unfold iterCost; omega]
  obtain ⟨img, hr, hfp⟩ := inv.img
  set k := Nat.toB256 (33 + i) with hk
  set b1 := afterSloadH sevm b k with hb1
  set b2 := afterSloadH sevm b1 k with hb2
  set z := zeroHash Bytes.sha256 i with hz
  set SS := sstoreCostH sevm b2 (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)) with hSS
  have hSSle : SS ≤ 20000 :=
    sstoreCostH_muir_le hmuir b2 _ _
  have hz0 : b.getStorVal sevm.currentTarget k = z := ctorStor_get inv.stor le_rfl (by omega)
  have hz1 : b1.getStorVal sevm.currentTarget k = z := by
    show (Devm.getStor b1 sevm.currentTarget).get k = z
    rw [hb1, afterSloadH_getStor]; exact hz0
  have hsize : M.size = memAt i := inv.size
  have hn32 : memAt i % 32 = 0 := by unfold memAt fp; split_ifs <;> omega
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    packed_sha_pairNMuir (fs := prog) (sevm := sevm) (C := [2]) (b := b2) (R := [Nat.toB256 i])
      (M := M) (G := G + 17 + SS + 44) (a := z) (bw := z) (n := memAt i) (f := fp i)
      (T := t_00e6_c1) (fail1 := t_00c8_c1) (fail2 := t_00e2_c1)
      prog_1 (by decide) inv.wf hr hsize hn32 (by unfold memAt fp; split_ifs <;> omega)
      (by unfold memAt fp; split_ifs <;> omega) (by unfold fp; omega) (by unfold fp; omega)
      (by unfold fp; omega) hfp (by simp only [List.length_cons, List.length_nil, zero_add,
        Nat.one_lt_ofNat])
      hmuir hdepth (by omega)
  refine ⟨afterSstoreH sevm b' (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1)), M',
    ⟨?_, ?_, hwf', ⟨img', hr', ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [afterSstoreH_getStor_self, hpost.stor, hb2, hb1, afterSloadH_getStor, afterSloadH_getStor]
    exact ctorStor_succ inv.stor (by omega)
  · rw [afterSstoreH_error, hpost.error, hb2, hb1, afterSloadH_error, afterSloadH_error]
    exact inv.error
  · rw [hw', show fp i + 96 = fp (i + 1) by unfold fp; omega]
  · rw [hs']; unfold memAt fp; rw [ite_eq_right (by omega)]; omega
  · intro deletions hmeta
    have hbase := inv.metadata deletions hmeta
    have hacc : sevm.benvStat.rules.access = .flat istanbulAccessGas := by
      rw [hmuir]
      rfl
    have hbase2 : CreateRunMeta sevm.currentTarget deletions b2 := by
      simpa only [hb2, hb1, afterSloadH, hacc] using hbase
    have hsha : CreateRunMeta sevm.currentTarget deletions b' :=
      ⟨hpost.refund.trans hbase2.refund, hpost.logs.trans hbase2.logs,
        hpost.deletions.trans hbase2.deletions, by rw [hpost.created]; exact hbase2.created⟩
    apply hsha.afterSstoreH
    change (Devm.getStor b' sevm.currentTarget).get (Nat.toB256 (34 + i)) = 0
    rw [hpost.stor, hb2, hb1, afterSloadH_getStor, afterSloadH_getStor,
      inv.stor, toNat_toB256' (by omega), ite_eq_right (by omega)]
  -- the loop head: `i < 31`, fall through into the body
  unfold t_0014_c2
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_lt (v := 1) ?_ (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  · rw [show Bytes.toB256 [0x1f] = Nat.toB256 31 by decide, lt_toB256 (by omega) (by omega),
      ite_eq_left hi]
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_zero ?_
  -- the two bounds-checked reads of `zero_hashes[i]`
  unfold t_001e_c2
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_lt (v := 1) ?_ (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      ite_eq_left (by omega)]
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_002c_c2
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_sload_selH (by rw [hmuir]; rfl) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [hz0]
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_lt (v := 1) ?_ (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      ite_eq_left (by omega)]
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_succ (by decide) ?_
  rw [t_003b_c2_eq]
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_sload_selH (by rw [hmuir]; rfl) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [hz1]
  -- the packed-hash site, then its continuation
  refine hrun _ ?_
  unfold t_00e6_c1
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := zeroHash Bytes.sha256 (i + 1)) ?_ ?_ ?_ (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  · rw [toNat_toB256' (by unfold fp; omega)]
    exact charge_covered hs' (by unfold fp; omega) (by omega)
  · rw [toNat_toB256' (by unfold fp; omega)]; exact read_word hr' _ hh'
  · rw [toNat_toB256' (by unfold fp; omega)]
    exact read_covered hs' (by unfold fp; omega) (by omega)
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_add' (toB256_add_push (c := 1) (by decide) (by omega)) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_lt (v := 1) ?_ (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by omega),
      ite_eq_left (by omega)]
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_00f8_c1
  refine rxc_dest ?_
  refine rxc_add' (toB256_add_push (c := 33) (by decide) (by omega)) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  rw [show 33 + (1 + i) = 34 + i by omega]
  rw [hSS, sstoreCostH_congr (d1 := b2) (d2 := b') _ _ hpost.keys.symm (hpost.stor _).symm
    hpost.created.symm]
  refine rxc_sstoreH (by rw [hmuir]; rfl)
    (fun _ => by unfold gCallStipend; omega) hstatic ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  exact rxc_jumpCut (by simp only [List.mem_cons, List.not_mem_nil, or_false])

/-- An iteration costs at most 24,000 gas: two flat `SLOAD`s at 800 gas, one
`SSTORE` at most 20,000 gas, the packed-hash site and the memory growth. -/
theorem iterCost_le {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules) (b : Devm) {i : Nat} (hi : i < 31) :
    iterCost sevm b i ≤ 24000 := by
  have hm : calculateMemoryGasCost (fp i + 192) - calculateMemoryGasCost (memAt i) ≤ 319 :=
    le_trans (Nat.sub_le _ _) (le_trans (calculateMemoryGasCost_mono
      (show fp i + 192 ≤ 3200 by unfold fp; omega)) (by decide))
  unfold iterCost
  have := sloadCostH_muir_eq hmuir b (Nat.toB256 (33 + i))
  have := sloadCostH_muir_eq hmuir (afterSloadH sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i))
  have := sstoreCostH_muir_le hmuir (afterSloadH sevm (afterSloadH sevm b (Nat.toB256 (33 + i))) (Nat.toB256 (33 + i)))
    (Nat.toB256 (34 + i)) (zeroHash Bytes.sha256 (i + 1))
  omega

/-! ## The last pass: copy out and return the runtime -/

/-- **The last pass** (`i = 31`): the loop test fails, the constructor copies the appended
runtime to memory `0` and returns it. -/
theorem exit {sevm : Sevm} (hcode : sevm.code = code) {b : Devm} {M : Mem}
    (herr : b.error = none) (hwf : Mem.Wf M) {img : Bytes} (hr : Mem.Reads M img)
    (hs : M.size = 3200) (G : Nat) :
    ∃ post, SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 31] M (G + exitCost)) t_0014_c2
        (.done (.halted post)) ∧
      post.output = runtimeWindow ∧ post.error = none ∧
      Devm.getStor post sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
      post.gasLeft = G ∧ (∀ target deletions, CreateRunMeta target deletions b →
        CreateRunMeta target deletions post) := by
  set M2 := M.write 0 runtimeWindow with hM2
  have hs2 : M2.size = 6368 := by
    rw [hM2, Mem.size_write_of_size hs (by decide) runtimeWindow_length]; decide
  have hr2 : Mem.Reads M2 (Bytes.writeAt img 0 runtimeWindow) := hr.write hwf 0 _
  have hout : (M2.read 0 6358).1 = runtimeWindow := by
    rw [hr2.read]
    have := Bytes.sliceD_writeAt img runtimeWindow 0
    rwa [runtimeWindow_length] at this
  obtain ⟨p1, p2, p3, p4⟩ :=
    returnPost_facts (St b [Nat.toB256 0, Nat.toB256 6358] M2 G) (Nat.toB256 0) (Nat.toB256 6358) []
  simp only [St.memory, toNat_toB256' (show 6358 < 2 ^ 256 by decide),
    toNat_toB256' (show 0 < 2 ^ 256 by decide), hout] at p1
  refine ⟨returnPost (St b [Nat.toB256 0, Nat.toB256 6358] M2 G) (Nat.toB256 0) (Nat.toB256 6358)
    [], ?_, p1, p2.trans herr, p3 _, p4, fun target deletions h =>
      (h.st _ _ _).returnPost _ _ _⟩
  rw [show G + exitCost = G + 3 + copyCost + 41 by unfold exitCost; omega]
  unfold t_0014_c2
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_lt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_0102_c2
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_push (w := Nat.toB256 6358) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_push (w := Nat.toB256 275) (by decide) (by simp only [List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLT]) ?_
  refine .next (Ninst.runCompiled_codecopy_of (s := [Nat.toB256 6358]) (G := G + 3)
    (c := copyCost) (M := M2) rfl ?_ ?_ rfl) ?_
  · rw [St.extCost_eq hs]
    simp only [toNat_toB256' (show 6358 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide)]
    rfl
  · simp only [St.memory, toNat_toB256' (show 6358 < 2 ^ 256 by decide),
      toNat_toB256' (show 0 < 2 ^ 256 by decide), toNat_toB256' (show 275 < 2 ^ 256 by decide),
      hcode, hM2, runtimeWindow]
  change SFunc.RunExactCut prog sevm [2] (St b [Nat.toB256 6358] M2 (G + 3)) _ _
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_return_any rfl ?_
  rw [St.extCost_eq hs2]
  simp only [toNat_toB256' (show 6358 < 2 ^ 256 by decide),
    toNat_toB256' (show 0 < 2 ^ 256 by decide)]
  decide

/-- The gas a loop-head state carries before iteration `i`: 24,000 per remaining iteration
and 1,280,000 for the last pass and the code deposit (`6358 · 200 = 1,271,600`). -/
def need (i : Nat) : Nat := 1280000 + (31 - i) * 24000

/-- A loop-head state before iteration `i`. -/
def LoopAt (sevm : Sevm) (initial : Devm) (i : Nat) (devm : Devm) : Prop :=
  ∃ b M G, devm = St b [Nat.toB256 i] M G ∧ LoopInv sevm initial i b M ∧ need i ≤ G ∧ G < 2 ^ 64

/-- **The loop**: 31 iterations through entry 2, then the last pass. -/
theorem loop {sevm : Sevm} {initial : Devm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false) (hcode : sevm.code = code) :
    ∀ devm, LoopAt sevm initial 0 devm → ∃ r, SFunc.RunExactCut prog sevm [] devm t_0014_c2 r ∧
      ∃ post, r = .done (.halted post) ∧ Done sevm post ∧
        (∀ deletions, CreateRunMeta sevm.currentTarget deletions initial →
          CreateRunMeta sevm.currentTarget deletions post) := by
  refine SFunc.RunExactCut.iterate prog_2 (by simp only [List.not_mem_nil, not_false_eq_true]) (LoopAt sevm initial) 31 _ ?_ ?_
  · rintro i hi _ ⟨b, M, G, rfl, inv, hneed, hGb⟩
    have hle := iterCost_le hmuir b hi
    have hn : 1280000 + (31 - i) * 24000 ≤ G := hneed
    obtain ⟨b', M', inv', run⟩ := iter hmuir hdepth hstatic hi inv (G := G - iterCost sevm b i) (by omega)
      (by omega)
    refine ⟨_, ?_, b', M', G - iterCost sevm b i, rfl, inv', ?_, by omega⟩
    · have e : St b [Nat.toB256 i] M G =
          St b [Nat.toB256 i] M (G - iterCost sevm b i + iterCost sevm b i) := by
        congr 1; omega
      rw [e]
      exact run
    · show 1280000 + (31 - (i + 1)) * 24000 ≤ G - iterCost sevm b i
      exact Nat.le_sub_of_add_le (by omega)
  · rintro _ ⟨b, M, G, rfl, inv, hneed, hGb⟩
    have hn : 1280000 + (31 - 31) * 24000 ≤ G := hneed
    have hle : exitCost ≤ G := by rw [exitCost_eq]; omega
    obtain ⟨img, hr, -⟩ := inv.img
    obtain ⟨post, run, hout, herr, hstor, hgas, hmeta⟩ :=
      exit hcode inv.error inv.wf hr (inv.size.trans memAt_31) (G - exitCost)
    refine ⟨_, ?_, fun d h => Seg.noConfusion h, post, rfl, ⟨hout, herr, ?_, ?_, ?_⟩, ?_⟩
    · have e : St b [Nat.toB256 31] M G = St b [Nat.toB256 31] M (G - exitCost + exitCost) := by
        congr 1; omega
      rw [e]
      exact run
    · rw [hstor]; exact inv.stor
    · rw [hgas, exitCost_eq]; omega
    · rw [hgas]; omega
    · intro deletions h
      exact hmeta _ _ (inv.metadata deletions h)

/-- The world facts the constructor needs at entry. -/
structure CtorStart (sevm : Sevm) (b : Devm) : Prop where
  code : sevm.code = code
  value : sevm.value = 0
  stor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0
  error : b.error = none

/-- **The constructor, gas-exact**: from an empty stack and memory with at least
`need 0 + 45` gas (and less than `2^64`), the lifted constructor halts, returning the runtime
window, with no error, the 32-entry zero-hash table in storage and at least 1,271,600 gas
left. -/
theorem ctor_run_meta {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false) {b : Devm} (st : CtorStart sevm b)
    {G : Nat} (hG : need 0 ≤ G) (hGb : G < 2 ^ 64) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + 45)) post ∧ Done sevm post ∧
      (∀ deletions, CreateRunMeta sevm.currentTarget deletions b →
        CreateRunMeta sevm.currentTarget deletions post) := by
  have hs0 : mem0.size = 96 := by rw [mem0, Mem.size_write_word_at]; rfl
  have hr0 : Mem.Reads mem0 (Bytes.writeAt [] 64 (Nat.toB256 128).toBytes) :=
    Mem.reads_empty.write Mem.wf_empty 64 _
  have hfp0 : (Bytes.writeAt [] 64 (Nat.toB256 128).toBytes).sliceD 64 32 0 =
      (Nat.toB256 (fp 0)).toBytes := by
    have := Bytes.sliceD_writeAt [] (Nat.toB256 128).toBytes 64
    rwa [B256.length_toBytes] at this
  obtain ⟨r, run, post, rfl, hpost, hmeta⟩ := loop (initial := b) hmuir hdepth hstatic st.code (St b [Nat.toB256 0] mem0 G)
    ⟨b, mem0, G, rfl, ⟨ctorStor_zero st.stor, st.error,
      Mem.wf_empty.write _ _, ⟨_, hr0, hfp0⟩, hs0, fun _ h => h⟩, hG, hGb⟩
  refine ⟨post, ⟨t_0000_c0, rfl, SFunc.runExact_iff_runExactCut_nil.mpr ?_⟩, hpost, hmeta⟩
  unfold t_0000_c0
  refine rxc_push (w := Nat.toB256 128) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  refine rxc_push (w := Nat.toB256 64) (by decide) (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.one_lt_ofNat]) ?_
  refine rxc_mstore (c := 12) (M' := mem0) ?_ rfl ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]; decide
  refine rxc_callvalue (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  rw [st.value]
  refine rxc_dup (n := 0) rfl (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.one_lt_ofNat]) ?_
  refine rxc_push rfl (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT]) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_push (w := Nat.toB256 0) (by decide) (by simp only [List.length_nil, Nat.ofNat_pos]) ?_
  rw [t_0014_c0_eq]
  exact run

/-- Compatibility projection of the constructor run without metadata. -/
theorem ctor_run {sevm : Sevm} (hmuir : sevm.benvStat.rules = muirGlacierRules)
    (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false) {b : Devm} (st : CtorStart sevm b)
    {G : Nat} (hG : need 0 ≤ G) (hGb : G < 2 ^ 64) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + 45)) post ∧ Done sevm post := by
  obtain ⟨post, run, done, -⟩ := ctor_run_meta hmuir hdepth hstatic st hG hGb
  exact ⟨post, run, done⟩

end Blanc.Lift.BeaconDeposit.Creation.Historical
