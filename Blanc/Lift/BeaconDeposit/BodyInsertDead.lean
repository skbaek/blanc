import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.PackedShaCovered

/-!
# Body segment 7: one hashing iteration of the insertion loop

One pass of the insertion loop at a height `h` whose size bit is clear: from the loop head
(pc `0x0f6e`, tree `t_0f6e_c23`, entry 23) back to it.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The insertion loop's copy entry: the solc word-copy loop at `0x0fe8` whose exit merges and
calls the precompile, returning to the loop head through `t_1097_c22`. -/
private theorem prog_22 : prog[22]? = some (mcpyTree 0x10 0x25 0x0f 0xe8 22
    (mergeTree (shaCallTree 0x10 0x82 0x10 0x97 t_1079_c22 t_1093_c22 t_1097_c22))) := rfl

private theorem prog_23 : prog[23]? = some t_0f6e_c23 := rfl

private theorem one_add_toB256' {h : Nat} (hh : h + 1 < 2 ^ 256) :
    Bytes.toB256 [0x01] + Nat.toB256 h = Nat.toB256 (h + 1) := by
  rw [show Bytes.toB256 [0x01] = Nat.toB256 1 by decide, toB256_add_toB256 (by omega),
    Nat.add_comm]

/-- The dead arm's hashing block: the key, the `SLOAD`, and `packed_sha_pair`'s shape (the
first copy pass inlined in entry 23 is entry 22's). -/
private theorem t_0faf_c23_eq : t_0faf_c23 = .dest (.next (.reg .add) (.next (.reg .sload)
    (.next (.reg (.dup 4)) (pack2Tree (mcpyTree 0x10 0x25 0x0f 0xe8 22
      (mergeTree (shaCallTree 0x10 0x82 0x10 0x97 t_1079_c22 t_1093_c22 t_1097_c22))))))) := rfl

-- SEGMENT: insertDead
/-- **Segment 7 (`0x0f6e → 0x0f6e`, one pass: trees `t_0f6e_c23`, `t_0f78_c23`, `t_0fa0_c23`,
`t_0faf_c23`, `t_0fe8_c23`, loop entry 22, back through `.jump 23`).**  At height `h < 32` with
`size` even: the head test `h < 32`, the bit test `size & 1 == 1` fails, the bounds check
`h < 32` (over `INVALID`), `SLOAD branch[h]`, the pair `branch[h] ‖ node` packed at the free
pointer `fp = 928 + 96 h` (words at `fp + 0x20`, `fp + 0x40`, length at `fp`, free pointer to
`fp + 0x60`), copied by the count-down word loop (first pass inlined in entry 23's tree, second
pass and exit in entry 22), the empty partial word merged (its `MLOAD` extends memory by the
last word), `STATICCALL` to the SHA-256 precompile, both checks; then `size / 2`, `h + 1` and
`JUMP` to the head.  Memory grows by 96 bytes.  `deadGas h` and the `SLOAD`.

Proof sketch.  Straight-line `rx_*` steps with `Ninst.runCompiled_sload_selected` (the
`SLOAD`'s charge `sloadCost`, successor `afterSload`), the packed-copy + precompile shape of
segment 3 (both copy passes unrolled with `rx_jump`: `prog[22] = t_0fe8_c22`), and
`rx_jump` with `prog[23] = t_0f6e_c23` at the end.  The memory expansion charges telescope to
`deadGas h`'s difference (sizes `1024 + 96 h → 1088 + 96 h → 1120 + 96 h`).  The stored slot is
`Nat.toB256 h + 0 = solBranchSlot h`; the digest is `hashPair` of the loaded word and `nd`. -/
theorem body_insertDead {sevm : Sevm} {b : Devm} {sz nd : B256} {R : List B256} {h G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hh : h < 32) (hsz : sz.toNat % 2 = 0) (hR : R.length ≤ 16)
    (hG : G + deadGas h + sloadCost sevm b (solBranchSlot h) < 2 ^ 256)
    (hM : BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) []) :
    ∃ b' M', Keep (afterSload sevm b (solBranchSlot h)) b' ∧
      BodyMem M' (1120 + 96 * h) (Nat.toB256 (1024 + 96 * h)) [] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' (Nat.toB256 (h + 1) :: sz / 2 ::
            BeaconDeposit.hashPair Bytes.sha256
              (b.getStorVal sevm.currentTarget (solBranchSlot h)) nd :: R) M' G) t_0f6e_c23 o →
        SFunc.RunExact prog sevm
          (St b (Nat.toB256 h :: sz :: nd :: R) M
            (G + (deadGas h + sloadCost sevm b (solBranchSlot h)))) t_0f6e_c23 o := by
  obtain ⟨hwf, hs, img, hr, hfp, -⟩ := hM
  have hhv : (Nat.toB256 h).toNat = h := B256.toNat_toB256_of_lt (by omega)
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hhv]
    exact (by show h < 32; omega)
  have hbit : (Bytes.toB256 [0x01] &&& sz) = 0 := by
    apply B256.toNat_inj
    rw [B256.toNat_and, show (Bytes.toB256 [0x01]).toNat = 1 from rfl, Nat.and_comm,
      Nat.and_one_is_mod, hsz]
    rfl
  have hkey : Nat.toB256 h + Bytes.toB256 [0x00] = solBranchSlot h := by
    apply B256.toNat_inj
    rw [B256.toNat_add, hhv, show (Bytes.toB256 [0x00]).toNat = 0 from rfl, Nat.add_zero,
      Nat.lo_eq_of_lt (by omega)]
    exact (B256.toNat_toB256_of_lt (by omega)).symm
  set b1 := afterSload sevm b (solBranchSlot h) with hb1
  have hok1 : ShaReady sevm b1 := ⟨by rw [hb1, afterSload_getCode]; exact hsha.nodeleg,
    by rw [hb1, afterSload_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.fork, hsha.depth⟩
  set br := b.getStorVal sevm.currentTarget (solBranchSlot h) with hbr
  have hfp' : img.sliceD 64 32 0 = (Nat.toB256 (928 + 96 * h)).toBytes := hfp
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    packed_sha_pair (fs := prog) (sevm := sevm) (C := []) (b := b1)
      (R := Nat.toB256 h :: sz :: nd :: R) (M := M) (G := G + 44)
      (e0 := 0x10) (e1 := 0x25) (r0 := 0x0f) (r1 := 0xe8) (c0 := 0x10) (c1 := 0x82)
      (v0 := 0x10) (v1 := 0x97) (k := 22) (fail1 := t_1079_c22) (fail2 := t_1093_c22)
      (T := t_1097_c22) (img := img) (n := 1024 + 96 * h) (f := 928 + 96 * h) (a := br)
      (bw := nd)
      prog_22 (by simp) hwf hr hs (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hfp' (by simp; omega) hok1.nodeleg hok1.warm hok1.pre hok1.fork hok1.depth
      (by unfold deadGas at hG; omega)
  refine ⟨b', M', ⟨hpost.stor, hpost.code, hpost.addrs, hpost.keys, hpost.logs, hpost.output,
    hpost.error⟩, ⟨hwf', by rw [hs']; omega, img', hr', by rw [hw']; congr 2; omega,
      by simp⟩, fun o k => ?_⟩
  rw [SFunc.runExact_iff_runExactCut_nil] at k ⊢
  unfold deadGas
  rw [show G + (867 + (calculateMemoryGasCost (1120 + 96 * h) -
      calculateMemoryGasCost (1024 + 96 * h)) + sloadCost sevm b (solBranchSlot h)) =
    (G + 44 + (727 + (calculateMemoryGasCost (928 + 96 * h + 192) -
      calculateMemoryGasCost (1024 + 96 * h)))) + 3 + sloadCost sevm b (solBranchSlot h) + 93 by
    rw [show 928 + 96 * h + 192 = 1120 + 96 * h by omega]; omega]
  unfold t_0f6e_c23
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt hlt (by simp; omega) ?_
  refine rxc_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_zero ?_
  unfold t_0f78_c23
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_and hbit (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_eq (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  unfold t_0fa0_c23
  refine rxc_dest ?_
  refine rxc_push (w := 2) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt hlt (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  rw [t_0faf_c23_eq]
  refine rxc_dest ?_
  refine rxc_add' hkey (by simp; omega) ?_
  refine rxc_sload_sel hsha.fork (by simp; omega) ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine hrun _ ?_
  unfold t_1097_c22
  have hF : (Nat.toB256 (928 + 96 * h + 96)).toNat = 928 + 96 * h + 96 :=
    toNat_toB256' (by omega)
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_mload (c := 3) (v := BeaconDeposit.hashPair Bytes.sha256 br nd) ?_
    (by rw [hF]; exact read_word hr' _ hh') ?_ (by simp; omega) ?_
  · rw [hF]; exact charge_covered hs' (by omega) (by omega)
  · rw [hF]; exact read_covered hs' (by omega) (by omega)
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_div (v := sz / 2) (by rw [show Bytes.toB256 [0x02] = 2 by decide])
    (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (one_add_toB256' (by omega)) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  exact rxc_jump prog_23 (by simp) k

end Blanc.Lift.BeaconDeposit
