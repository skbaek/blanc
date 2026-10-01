import Blanc.Lift.PackedSha
import Blanc.Lift.BeaconDeposit.Prog
import Blanc.Lift.BeaconDeposit.Layout
import Blanc.WordArithmetic

/-!
# One iteration of `get_deposit_root`'s Merkle loop on the deployed contract

The loop of `get_deposit_root` (source lines 83–89) is entry 24 of the lifted program (pc
`0x10d1`), with the stack `height :: size :: node :: …` at its head.  One iteration below
height 32 tests the low bit of `size`, reads `branch[height]` (slot `height`, live bit) or
`zero_hashes[height]` (slot `33 + height`, dead bit), hashes the pair with the precompile at
address 2 (`packed_sha_pair`, through the copy loops at entries 27 and 28), halves `size`,
increments `height` and jumps back.

The memory grows by three words per iteration (solc 0.6 never frees the `abi.encodePacked`
buffers): the free pointer is `rootFp h = 0x80 + 0x60·h` at the head of iteration `h`, and
memory has `rootMemSize h` bytes.

`root_iter` is the iteration as an exact run cut at the loop head: 878 gas on the live arm and
868 on the dead one, the selected `SLOAD`'s warm or cold charge, and the memory expansion
`rootIterMem h`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.BeaconDeposit

/-! ## The iteration's state and cost -/

/-- The free pointer at the head of iteration `h`. -/
def rootFp (h : Nat) : Nat := 128 + 96 * h

/-- The memory size at the head of iteration `h` (the dispatcher's `mstore(0x40, 0x80)` leaves
three words; every iteration adds three). -/
def rootMemSize (h : Nat) : Nat := if h = 0 then 96 else 224 + 96 * h

/-- The storage key iteration `h` reads for the running `size`. -/
def rootKey (size h : Nat) : B256 :=
  if size % 2 = 1 then solBranchSlot h else solZeroHashSlot h

/-- The memory expansion charge of iteration `h`. -/
def rootIterMem (h : Nat) : Nat :=
  calculateMemoryGasCost (rootFp h + 192) - calculateMemoryGasCost (rootMemSize h)

/-- The gas of iteration `h` with the access set `keys`: 878 (live) or 868 (dead), the
`SLOAD` of `rootKey size h`, and the expansion. -/
def rootIterGas (owner : Adr) (keys : KeySet) (size h : Nat) : Nat :=
  (if size % 2 = 1 then 878 else 868) + sloadCostOfKeys owner keys (rootKey size h) +
    rootIterMem h

/-- The node iteration `h` computes from the storage it reads. -/
def rootNode (sevm : Sevm) (b : Devm) (size h : Nat) (node : B256) : B256 :=
  if size % 2 = 1 then hashPair Bytes.sha256 (b.getStorVal sevm.currentTarget (solBranchSlot h)) node
  else hashPair Bytes.sha256 node (b.getStorVal sevm.currentTarget (solZeroHashSlot h))

theorem baseRel_afterSload (sevm : Sevm) (b : Devm) (k : B256) :
    BaseRel b (afterSload sevm b k) :=
  ⟨afterSload_getStor sevm b k, afterSload_getCode sevm b k, afterSload_accessedAddresses sevm b k,
    afterSload_logs sevm b k, afterSload_output sevm b k, afterSload_error sevm b k⟩

/-! ## The trees -/

/-- The live-arm hash tail (entry 27's exit). -/
abbrev liveExit : SFunc :=
  mergeTree (shaCallTree 0x11 0xc8 0x11 0xdd t_11bf_c24 t_11d9_c24 t_11dd_c24)

/-- The dead-arm hash tail (entry 28's exit). -/
abbrev deadExit : SFunc :=
  mergeTree (shaCallTree 0x12 0xc8 0x12 0xdd t_12bf_c24 t_12d9_c24 t_12dd_c24)

theorem prog_27 : prog[27]? = some (mcpyTree 0x11 0x6b 0x11 0x2e 27 liveExit) := rfl

theorem prog_28 : prog[28]? = some (mcpyTree 0x12 0x6b 0x12 0x2e 28 deadExit) := rfl

theorem prog_5 : prog[5]? = some t_12e2_c5 := rfl

theorem prog_24 : prog[24]? = some t_10d1_c24 := rfl

theorem t_10f5_eq : t_10f5_c24 = .dest (.next (.reg .add) (.next (.reg .sload)
    (.next (.reg (.dup 4)) (pack2Tree (mcpyTree 0x11 0x6b 0x11 0x2e 27 liveExit))))) := rfl

theorem t_11f6_eq : t_11f6_c24 = .dest (.next (.reg .add) (.next (.reg .sload)
    (pack2Tree (mcpyTree 0x12 0x6b 0x12 0x2e 28 deadExit)))) := rfl

/-! ## Arithmetic -/

theorem rootFp_succ (h : Nat) : rootFp h + 96 = rootFp (h + 1) := by unfold rootFp; omega

theorem rootMemSize_succ (h : Nat) : rootFp h + 192 = rootMemSize (h + 1) := by
  unfold rootFp rootMemSize; simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; omega

theorem rootMemSize_le (h : Nat) : rootMemSize h ≤ rootFp h + 96 := by
  unfold rootFp rootMemSize; split <;> omega

theorem rootMemSize_mod (h : Nat) : rootMemSize h % 32 = 0 := by
  unfold rootMemSize; split <;> omega

theorem rootMemSize_ge (h : Nat) : 96 ≤ rootMemSize h := by
  unfold rootMemSize; split <;> omega

theorem eq_one_mod_two (s : Nat) :
    B256.eqCheck (Bytes.toB256 [0x01]) (Nat.toB256 (s % 2)) = if s % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h] <;> decide

/-! ## The iteration -/

section Iter

variable {sevm : Sevm} {R : List B256} {M : Mem} {G : Nat}

/-- The join (entry 5): `size / 2`, `height + 1`, and the back-edge. 34 gas. -/
theorem root_join {b : Devm} {h s : Nat} {x : B256} (hh : h + 1 < 2 ^ 256) (hs : s < 2 ^ 256)
    (hR : R.length < 1000) :
    SFunc.RunExactCut prog sevm [24] (St b (Nat.toB256 h :: Nat.toB256 s :: x :: R) M (G + 34))
      t_12e2_c5 (.at 24 (St b (Nat.toB256 (h + 1) :: Nat.toB256 (s / 2) :: x :: R) M G)) := by
  unfold t_12e2_c5
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_div (show Nat.toB256 s / Bytes.toB256 [0x02] = Nat.toB256 (s / 2) by
    rw [show Bytes.toB256 [0x02] = (2 : B256) by decide, toB256_div_two hs]) (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod,
    List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_add' (one_add_toB256 hh) (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.set_cons_zero, List.length_cons]; omega) ?_
  exact rxc_jumpCut (by simp only [List.mem_cons, List.not_mem_nil, or_false])

/-- What one iteration leaves: the world related by `BaseRel`, the selected key warm, and the
next iteration's memory. -/
def IterPost (sevm : Sevm) (b b' : Devm) (key : B256) (h : Nat) (M' : Mem) : Prop :=
  BaseRel b b' ∧
    b'.accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget b.accessedStorageKeys key ∧
    Mem.Wf M' ∧ M'.size = rootMemSize (h + 1) ∧
    ∃ img', Mem.Reads M' img' ∧
      img'.sliceD 64 32 0 = (Nat.toB256 (rootFp (h + 1))).toBytes

theorem root_iter_live {b : Devm} {h size : Nat} {node : B256} {img : Bytes}
    (hh : h < 32) (hsize : size < 2 ^ 32) (hodd : size % 2 = 1)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = rootMemSize h)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 (rootFp h)).toBytes) (hR : R.length < 800)
    (hok : ShaReady sevm b) (hdepth : sevm.depth ≠ 0) (hG : G + 2000 < 2 ^ 256) :
    ∃ b' M', IterPost sevm b b' (rootKey size h) h M' ∧
      SFunc.RunExactCut prog sevm [24]
        (St b (Nat.toB256 h :: Nat.toB256 size :: node :: R) M
          (G + rootIterGas sevm.currentTarget b.accessedStorageKeys size h))
        t_10d1_c24
        (.at 24 (St b' (Nat.toB256 (h + 1) :: Nat.toB256 (size / 2) ::
          rootNode sevm b size h node :: R) M' G)) := by
  have hkey : rootKey size h = Nat.toB256 h := by simp only [rootKey, hodd, ↓reduceIte,
    solBranchSlot]
  set b1 := afterSload sevm b (Nat.toB256 h) with hb1
  have hrel1 := baseRel_afterSload sevm b (Nat.toB256 h)
  have hok1 := hok.of_rel hrel1
  set br := b.getStorVal sevm.currentTarget (Nat.toB256 h) with hbr
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    packed_sha_pair (fs := prog) (sevm := sevm) (C := [24]) (b := b1)
      (R := Nat.toB256 h :: Nat.toB256 size :: node :: R) (M := M) (G := G + 56)
      (e0 := 0x11) (e1 := 0x6b) (r0 := 0x11) (r1 := 0x2e) (c0 := 0x11) (c1 := 0xc8)
      (v0 := 0x11) (v1 := 0xdd) (k := 27) (fail1 := t_11bf_c24) (fail2 := t_11d9_c24)
      (T := t_11dd_c24) (img := img) (n := rootMemSize h) (f := rootFp h) (a := br) (bw := node)
      prog_27 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
        not_false_eq_true]) hwf hr hs (rootMemSize_mod h) (rootMemSize_ge h) (rootMemSize_le h)
      (by unfold rootFp; omega) (by unfold rootFp; omega) (by unfold rootFp; omega) hfp
      (by simp only [List.length_cons]; omega) hok1.nodeleg hok1.warm hok1.pre hok1.fork hdepth (by omega)
  refine ⟨b', M', ⟨hrel1.trans (baseRel_sha hpost), ?_, hwf', ?_, img', hr', ?_⟩, ?_⟩
  · rw [hpost.keys, hb1, afterSload_accessedStorageKeys, hkey]
  · rw [hs', rootMemSize_succ]
  · rw [hw', rootFp_succ]
  have hnode : rootNode sevm b size h node = hashPair Bytes.sha256 br node := by
    simp only [rootNode, hodd, ↓reduceIte, solBranchSlot, hbr]
  rw [hnode]
  unfold rootIterGas
  simp only [hodd, ↓reduceIte]
  rw [hkey, sloadCostOfKeys_eq_sloadCost]
  rw [show G + (878 + sloadCost sevm b (Nat.toB256 h) + rootIterMem h) =
    G + 56 + (727 + rootIterMem h) + 3 + sloadCost sevm b (Nat.toB256 h) + 92 by omega]
  unfold t_10d1_c24 t_10db_c24 t_10e7_c24
  have h20 : Bytes.toB256 [0x20] = Nat.toB256 32 := by decide
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [h20, lt_toB256 (by omega) (by norm_num)]; simp only [hh, ↓reduceIte]
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt hlt (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_and (x := Bytes.toB256 [0x01]) (y := Nat.toB256 size)
    (v := Nat.toB256 (size % 2)) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [show Bytes.toB256 [0x01] = 1 by decide]
    exact Blanc.one_and_toB256_eq_mod_two size (by omega)
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_eq (v := 1) (by rw [eq_one_mod_two]; simp only [hodd, ↓reduceIte]) (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt hlt (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  rw [t_10f5_eq]
  refine rxc_dest ?_
  refine rxc_add' (v := Nat.toB256 h) ?_ (by simp only [List.length_cons]; omega) ?_
  · apply word_of_toNat _ (by omega)
    rw [B256.toNat_add, toNat_toB256' (by omega), show (Bytes.toB256 [0x00]).toNat = 0 by decide,
      Nat.add_zero, Nat.lo_eq_of_lt (by omega)]
  refine rxc_sload_sel hok.fork (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine hrun _ ?_
  unfold t_11dd_c24
  have hF : (Nat.toB256 (rootFp h + 96)).toNat = rootFp h + 96 :=
    toNat_toB256' (by unfold rootFp; omega)
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := hashPair Bytes.sha256 br node) ?_
    (by rw [hF]; exact read_word hr' _ hh') ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [hF]; exact charge_covered hs' (by unfold rootFp; omega) (by omega)
  · rw [hF]; exact read_covered hs' (by unfold rootFp; omega) (by omega)
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    List.set_cons_succ, List.set_cons_zero, List.length_cons]; omega) ?_
  refine rxc_jump prog_5 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
    not_false_eq_true]) ?_
  exact root_join (by omega) (by omega) (by omega)


theorem root_iter_dead {b : Devm} {h size : Nat} {node : B256} {img : Bytes}
    (hh : h < 32) (hsize : size < 2 ^ 32) (heven : size % 2 = 0)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = rootMemSize h)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 (rootFp h)).toBytes) (hR : R.length < 800)
    (hok : ShaReady sevm b) (hdepth : sevm.depth ≠ 0) (hG : G + 2000 < 2 ^ 256) :
    ∃ b' M', IterPost sevm b b' (rootKey size h) h M' ∧
      SFunc.RunExactCut prog sevm [24]
        (St b (Nat.toB256 h :: Nat.toB256 size :: node :: R) M
          (G + rootIterGas sevm.currentTarget b.accessedStorageKeys size h))
        t_10d1_c24
        (.at 24 (St b' (Nat.toB256 (h + 1) :: Nat.toB256 (size / 2) ::
          rootNode sevm b size h node :: R) M' G)) := by
  have hkey : rootKey size h = Nat.toB256 (33 + h) := by simp only [rootKey, heven, zero_ne_one,
    ↓reduceIte, solZeroHashSlot]
  set b1 := afterSload sevm b (Nat.toB256 (33 + h)) with hb1
  have hrel1 := baseRel_afterSload sevm b (Nat.toB256 (33 + h))
  have hok1 := hok.of_rel hrel1
  set zh := b.getStorVal sevm.currentTarget (Nat.toB256 (33 + h)) with hzh
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    packed_sha_pair (fs := prog) (sevm := sevm) (C := [24]) (b := b1)
      (R := Nat.toB256 h :: Nat.toB256 size :: node :: R) (M := M) (G := G + 45)
      (e0 := 0x12) (e1 := 0x6b) (r0 := 0x12) (r1 := 0x2e) (c0 := 0x12) (c1 := 0xc8)
      (v0 := 0x12) (v1 := 0xdd) (k := 28) (fail1 := t_12bf_c24) (fail2 := t_12d9_c24)
      (T := t_12dd_c24) (img := img) (n := rootMemSize h) (f := rootFp h) (a := node) (bw := zh)
      prog_28 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self,
        not_false_eq_true]) hwf hr hs (rootMemSize_mod h) (rootMemSize_ge h) (rootMemSize_le h)
      (by unfold rootFp; omega) (by unfold rootFp; omega) (by unfold rootFp; omega) hfp
      (by simp only [List.length_cons]; omega) hok1.nodeleg hok1.warm hok1.pre hok1.fork hdepth (by omega)
  refine ⟨b', M', ⟨hrel1.trans (baseRel_sha hpost), ?_, hwf', ?_, img', hr', ?_⟩, ?_⟩
  · rw [hpost.keys, hb1, afterSload_accessedStorageKeys, hkey]
  · rw [hs', rootMemSize_succ]
  · rw [hw', rootFp_succ]
  have hnode : rootNode sevm b size h node = hashPair Bytes.sha256 node zh := by
    simp only [rootNode, heven, zero_ne_one, ↓reduceIte, solZeroHashSlot, hzh]
  rw [hnode]
  unfold rootIterGas
  simp only [show ¬ size % 2 = 1 by omega, ↓reduceIte]
  rw [hkey, sloadCostOfKeys_eq_sloadCost]
  rw [show G + (868 + sloadCost sevm b (Nat.toB256 (33 + h)) + rootIterMem h) =
    G + 45 + (727 + rootIterMem h) + sloadCost sevm b (Nat.toB256 (33 + h)) + 96 by omega]
  unfold t_10d1_c24 t_10db_c24 t_11e6_c24
  have h20 : Bytes.toB256 [0x20] = Nat.toB256 32 := by decide
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [h20, lt_toB256 (by omega) (by norm_num)]; simp only [hh, ↓reduceIte]
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt hlt (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_and (x := Bytes.toB256 [0x01]) (y := Nat.toB256 size)
    (v := Nat.toB256 (size % 2)) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [show Bytes.toB256 [0x01] = 1 by decide]
    exact Blanc.one_and_toB256_eq_mod_two size (by omega)
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_eq (v := 0) (by rw [eq_one_mod_two]; simp only [heven, zero_ne_one, ↓reduceIte]) (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  refine rxc_dest ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt hlt (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  rw [t_11f6_eq]
  refine rxc_dest ?_
  refine rxc_add' (v := Nat.toB256 (33 + h)) ?_ (by simp only [List.length_cons]; omega) ?_
  · apply word_of_toNat _ (by omega)
    rw [B256.toNat_add, toNat_toB256' (by omega), show (Bytes.toB256 [0x21]).toNat = 33 by decide,
      Nat.lo_eq_of_lt (by omega), Nat.add_comm]
  refine rxc_sload_sel hok.fork (by simp only [List.length_cons]; omega) ?_
  refine hrun _ ?_
  unfold t_12dd_c24
  have hF : (Nat.toB256 (rootFp h + 96)).toNat = rootFp h + 96 :=
    toNat_toB256' (by unfold rootFp; omega)
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := hashPair Bytes.sha256 node zh) ?_
    (by rw [hF]; exact read_word hr' _ hh') ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [hF]; exact charge_covered hs' (by unfold rootFp; omega) (by omega)
  · rw [hF]; exact read_covered hs' (by unfold rootFp; omega) (by omega)
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  exact root_join (by omega) (by omega) (by omega)

/-- **One iteration** below height 32, either arm. -/
theorem root_iter {b : Devm} {h size : Nat} {node : B256} {img : Bytes}
    (hh : h < 32) (hsize : size < 2 ^ 32)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = rootMemSize h)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 (rootFp h)).toBytes) (hR : R.length < 800)
    (hok : ShaReady sevm b) (hdepth : sevm.depth ≠ 0) (hG : G + 2000 < 2 ^ 256) :
    ∃ b' M', IterPost sevm b b' (rootKey size h) h M' ∧
      SFunc.RunExactCut prog sevm [24]
        (St b (Nat.toB256 h :: Nat.toB256 size :: node :: R) M
          (G + rootIterGas sevm.currentTarget b.accessedStorageKeys size h))
        t_10d1_c24
        (.at 24 (St b' (Nat.toB256 (h + 1) :: Nat.toB256 (size / 2) ::
          rootNode sevm b size h node :: R) M' G)) := by
  rcases Nat.mod_two_eq_zero_or_one size with he | ho
  · exact root_iter_dead hh hsize he hwf hr hs hfp hR hok hdepth hG
  · exact root_iter_live hh hsize ho hwf hr hs hfp hR hok hdepth hG

end Iter

/-! ## The loop -/

/-- The access set after `k` iterations from height `h`. -/
def rootKeys (owner : Adr) : Nat → Nat → Nat → KeySet → KeySet
  | 0, _, _, keys => keys
  | k + 1, h, size, keys =>
      rootKeys owner k (h + 1) (size / 2) (sloadAccessedStorageKeys owner keys (rootKey size h))

/-- The gas of `k` iterations from height `h`. -/
def rootGas (owner : Adr) : Nat → Nat → Nat → KeySet → Nat
  | 0, _, _, _ => 0
  | k + 1, h, size, keys =>
      rootIterGas owner keys size h +
        rootGas owner k (h + 1) (size / 2) (sloadAccessedStorageKeys owner keys (rootKey size h))

theorem climb_succ (H : Bytes → B256) (br : Nat → B256) :
    ∀ k h s n, climb H br (k + 1) h s n =
      (if s / 2 ^ k % 2 = 1 then hashPair H (br (h + k)) (climb H br k h s n)
       else hashPair H (climb H br k h s n) (zeroHash H (h + k)))
  | 0, h, s, n => by simp only [climb, pow_zero, Nat.div_one, add_zero]
  | k + 1, h, s, n => by
      have e1 : climb H br (k + 1 + 1) h s n = climb H br (k + 1) (h + 1) (s / 2)
          (if s % 2 = 1 then hashPair H (br h) n else hashPair H n (zeroHash H h)) := rfl
      have e2 : climb H br (k + 1) h s n = climb H br k (h + 1) (s / 2)
          (if s % 2 = 1 then hashPair H (br h) n else hashPair H n (zeroHash H h)) := rfl
      rw [e1, e2, climb_succ H br k (h + 1) (s / 2), div_two_div_pow,
        show h + 1 + k = h + (k + 1) by omega]

theorem rootKeys_succ (owner : Adr) :
    ∀ k h s keys, rootKeys owner (k + 1) h s keys =
      sloadAccessedStorageKeys owner (rootKeys owner k h s keys) (rootKey (s / 2 ^ k) (h + k))
  | 0, h, s, keys => by simp only [rootKeys, pow_zero, Nat.div_one, add_zero]
  | k + 1, h, s, keys => by
      have e1 : rootKeys owner (k + 1 + 1) h s keys = rootKeys owner (k + 1) (h + 1) (s / 2)
          (sloadAccessedStorageKeys owner keys (rootKey s h)) := rfl
      have e2 : rootKeys owner (k + 1) h s keys = rootKeys owner k (h + 1) (s / 2)
          (sloadAccessedStorageKeys owner keys (rootKey s h)) := rfl
      rw [e1, e2, rootKeys_succ owner k (h + 1) (s / 2), div_two_div_pow,
        show h + 1 + k = h + (k + 1) by omega]

/-- The node an iteration computes, read against the Solidity-layout accumulator. -/
theorem rootNode_eq {sevm : Sevm} {b base : Devm} {stor : Stor} (hrel : BaseRel base b)
    (hstor : Devm.getStor base sevm.currentTarget = stor) (hzero : SolZeroHashesCorrect stor)
    {h : Nat} (hh : h < 32) (s : Nat) (node : B256) :
    rootNode sevm b s h node =
      if s % 2 = 1 then hashPair Bytes.sha256 ((solAcc stor).branch h) node
      else hashPair Bytes.sha256 node (zeroHash Bytes.sha256 h) := by
  have e : ∀ k, b.getStorVal sevm.currentTarget k = stor.get k := fun k => by
    rw [hrel.getStorVal]; show (Devm.getStor base sevm.currentTarget).get k = _; rw [hstor]
  unfold rootNode
  rw [e, e, hzero h hh]
  simp only [solAcc, hh, ↓reduceIte]

/-- The loop invariant at the head of iteration `i`. -/
def RootInv (sevm : Sevm) (base : Devm) (stor : Stor) (count : Nat) (keys0 : KeySet)
    (R : List B256) (Gx : Nat) (i : Nat) (devm : Devm) : Prop :=
  ∃ b M, devm = St b (Nat.toB256 i :: Nat.toB256 (count / 2 ^ i) ::
      climb Bytes.sha256 (solAcc stor).branch i 0 count 0 :: R) M
      (Gx + rootGas sevm.currentTarget (32 - i) i (count / 2 ^ i)
        (rootKeys sevm.currentTarget i 0 count keys0)) ∧
    BaseRel base b ∧ b.accessedStorageKeys = rootKeys sevm.currentTarget i 0 count keys0 ∧
    Mem.Wf M ∧ M.size = rootMemSize i ∧
    (∃ img, Mem.Reads M img ∧ img.sliceD 64 32 0 = (Nat.toB256 (rootFp i)).toBytes) ∧
    Gx + rootGas sevm.currentTarget (32 - i) i (count / 2 ^ i)
      (rootKeys sevm.currentTarget i 0 count keys0) + 2000 < 2 ^ 256

/-- **The loop**: 32 iterations from the head of iteration 0 (the loop's own entry 24, with
nothing else cut), then the exit tree from height 32, which may end any way `Q` admits. -/
theorem root_loop {sevm : Sevm} {base : Devm} {stor : Stor} {count : Nat} {R : List B256}
    {Gx : Nat} {Q : Seg → Prop}
    (hstor : Devm.getStor base sevm.currentTarget = stor) (hzero : SolZeroHashesCorrect stor)
    (hcount : count < 2 ^ 32) (hok : ShaReady sevm base)
    (hdepth : sevm.depth ≠ 0) (hR : R.length < 800)
    (hG : Gx + rootGas sevm.currentTarget 32 0 count base.accessedStorageKeys + 2000 < 2 ^ 256)
    (hexit : ∀ devm, RootInv sevm base stor count base.accessedStorageKeys R Gx 32 devm →
      ∃ r, SFunc.RunExactCut prog sevm [24] devm t_10d1_c24 r ∧ (∀ d, r ≠ .at 24 d) ∧ Q r)
    {M : Mem} {img : Bytes} (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = 96)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 128).toBytes) :
    ∃ r, SFunc.RunExactCut prog sevm []
      (St base (Nat.toB256 0 :: Nat.toB256 count :: 0 :: R) M
        (Gx + rootGas sevm.currentTarget 32 0 count base.accessedStorageKeys))
      t_10d1_c24 r ∧ Q r := by
  refine SFunc.RunExactCut.iterate (fs := prog) (sevm := sevm) (C := []) prog_24 (by simp only [List.not_mem_nil,
    not_false_eq_true])
    (RootInv sevm base stor count base.accessedStorageKeys R Gx) 32 Q ?_ hexit _
    ⟨base, M, by simp only [pow_zero, Nat.div_one, climb, tsub_zero, rootKeys], BaseRel.refl base, rfl, hwf, hs, ⟨img, hr, hfp⟩,
      by simpa only [tsub_zero, pow_zero, Nat.div_one, rootKeys, Nat.reducePow] using hG⟩
  intro i hi devm ⟨b, M, hdevm, hrel, hkeys, hwf, hs, ⟨img, hr, hfp⟩, hGi⟩
  have hsz : count / 2 ^ i < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hcount
  have hgas : rootGas sevm.currentTarget (32 - i) i (count / 2 ^ i)
      (rootKeys sevm.currentTarget i 0 count base.accessedStorageKeys) =
      rootIterGas sevm.currentTarget b.accessedStorageKeys (count / 2 ^ i) i +
        rootGas sevm.currentTarget (32 - (i + 1)) (i + 1) (count / 2 ^ (i + 1))
          (rootKeys sevm.currentTarget (i + 1) 0 count base.accessedStorageKeys) := by
    rw [show 32 - i = (32 - (i + 1)) + 1 by omega, rootGas, hkeys, rootKeys_succ,
      Nat.zero_add, div_pow_div_two]
  obtain ⟨b', M', ⟨hrel', hkeys', hwf', hs', img', hr', hfp'⟩, hrun⟩ :=
    root_iter (sevm := sevm) (b := b) (R := R) (G := Gx + rootGas sevm.currentTarget
      (32 - (i + 1)) (i + 1) (count / 2 ^ (i + 1))
        (rootKeys sevm.currentTarget (i + 1) 0 count base.accessedStorageKeys))
      (node := climb Bytes.sha256 (solAcc stor).branch i 0 count 0)
      hi hsz hwf hr hs hfp (by omega) (hok.of_rel hrel) hdepth (by omega)
  have hc := climb_succ Bytes.sha256 (solAcc stor).branch i 0 count 0
  rw [Nat.zero_add] at hc
  rw [div_pow_div_two, rootNode_eq hrel hstor hzero hi, ← hc] at hrun
  refine ⟨_, ?_, b', M', rfl, hrel.trans hrel', ?_, hwf', hs', ⟨img', hr', hfp'⟩, by omega⟩
  · rw [hdevm, hgas, show ∀ a c : Nat, Gx + (a + c) = Gx + c + a from fun a c => by omega]
    exact hrun
  · rw [hkeys', hkeys, rootKeys_succ, Nat.zero_add]

end Blanc.Lift.BeaconDeposit
