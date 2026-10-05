import Blanc.Lift.BeaconDeposit.BodyShaKit
import Blanc.Lift.InvWalkSha

/-!
# Safety segment L1: one hashing pass of the insertion loop, inverted
(converse of `body_insertDead`, as a cut run at the loop head)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeInsertDead
/-- **Inversion of a dead pass (`t_0f6e_c23` cut at entry 23).**  From the loop head at a height
`h ≤ 32` with `size` even, every successful cut run passes the head test (so `h < 32`) and ends
at the next head, one height up, with the combined node.

Proof sketch.  `cases` along `body_insertDead`'s walk with `SFunc.RunCutP` in place of `Run`
(the same constructors; `.jump 23` is `jumpCut`, the only way to `.at`; `.jump 22` is followed).
The head test `h < 32` has `t_10a9_c23 = POP; undefined` as its failing arm (no rule).  The bit
test is decided by `hsz` (`Nat.and_one_is_mod` through `B256.toNat_and`, as in
`body_insertLive`).  The precompile block as in segment B3's sketch; the `SLOAD` of
`Nat.toB256 h + 0 = solBranchSlot h` has successor `afterSload`. -/
theorem safe_insertDead {sevm : Sevm} {b : Devm} {sz nd : B256} {R : List B256} {h G : Nat}
    {M : Mem} {r : Seg}
    (hsha : ShaReady sevm b) (hh : h ≤ 32) (hsz : sz.toNat % 2 = 0) (hR : R.length ≤ 16)
    (hM : BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) [])
    (run : SFunc.RunCut prog sevm [23] (St b (Nat.toB256 h :: sz :: nd :: R) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' M' G', Keep (afterSload sevm b (solBranchSlot h)) b' ∧
      BodyMem M' (1120 + 96 * h) (Nat.toB256 (1024 + 96 * h)) [] ∧
      r = .at 23 (St b' (Nat.toB256 (h + 1) :: sz / 2 ::
        BeaconDeposit.hashPair Bytes.sha256
          (b.getStorVal sevm.currentTarget (solBranchSlot h)) nd :: R) M' G') := by
  -- the stack bound is the forward walk's; no inverted step needs it
  have _ := hR
  obtain ⟨hwf, hs, img, hr, hfp, -⟩ := hM
  have hhv : (Nat.toB256 h).toNat = h := B256.toNat_toB256_of_lt (by omega)
  have hbit : (Bytes.toB256 [0x01] &&& sz) = 0 := by
    apply B256.toNat_inj
    rw [B256.toNat_and, show (Bytes.toB256 [0x01]).toNat = 1 from rfl, Nat.and_comm,
      Nat.and_one_is_mod, hsz]
    rfl
  -- t_0f6e_c23: the head test
  unfold t_0f6e_c23 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := Nat.toB256 h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  have hh32 : h < 32 := by
    rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G7, run'⟩
    · by_contra hge
      have : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 0 := by
        rw [B256.ltCheck, ite_eq_right]
        rw [B256.lt_iff_toNat_lt_toNat, hhv]
        exact (by show ¬ h < 32; omega)
      rw [this] at hw
      exact absurd hw (by decide)
    · exfalso
      unfold t_10a9_c23 at run'
      obtain ⟨G8, run'⟩ := ric_dest run'
      obtain ⟨d2, -, run'⟩ := ric_next run'
      exact ric_undefined run'
  refine ⟨hh32, ?_⟩
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hhv]
    exact (by show h < 32; omega)
  have hkey : Nat.toB256 h + Bytes.toB256 [0x00] = solBranchSlot h := by
    apply B256.toNat_inj
    rw [B256.toNat_add, hhv, show (Bytes.toB256 [0x00]).toNat = 0 from rfl, Nat.add_zero,
      Nat.lo_eq_of_lt (by omega)]
    exact (B256.toNat_toB256_of_lt (by omega)).symm
  rw [hlt] at run
  rcases ric_branch run with ⟨-, G7, run⟩ | ⟨hw, -⟩
  swap; · exact absurd hw (by decide)
  -- t_0f78_c23: the bit test
  unfold t_0f78_c23 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := sz) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  rw [hbit, show B256.eqCheck (Bytes.toB256 [0x01]) 0 = 0 by decide,
    show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  -- t_0fa0_c23: the bounds check
  unfold t_0fa0_c23 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := Nat.toB256 h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := Nat.toB256 h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  rw [hlt] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, _, run⟩
  · exact absurd hw (by decide)
  -- t_0faf_c23: the key, the `SLOAD`, the packed pair and the precompile call
  rw [show t_0faf_c23 = .dest (.next (.reg .add) (.next (.reg .sload)
      (.next (.reg (.dup 4)) (pack2Tree (mcpyTree 0x10 0x25 0x0f 0xe8 22
        (mergeTree (shaCallTree 0x10 0x82 0x10 0x97 t_1079_c22 t_1093_c22 t_1097_c22)))))))
    from rfl] at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_add s1
  rw [hkey] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sload hsha.fork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  set b1 := afterSload sevm b (solBranchSlot h) with hb1
  have hok1 : ShaReady sevm b1 := ⟨by rw [hb1, afterSload_getCode]; exact hsha.nodeleg,
    by rw [hb1, afterSload_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.fork⟩
  set br := b.getStorVal sevm.currentTarget (solBranchSlot h) with hbr
  have hfp' : img.sliceD 64 32 0 = (Nat.toB256 (928 + 96 * h)).toBytes := hfp
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_pack_sha (a := br) (bw := nd)
    (n := 1024 + 96 * h) (f := 928 + 96 * h)
    (show prog[22]? = some (mcpyTree 0x10 0x25 0x0f 0xe8 22
      (mergeTree (shaCallTree 0x10 0x82 0x10 0x97 t_1079_c22 t_1093_c22 t_1097_c22))) from rfl)
    (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, not_false_eq_true]) (by decide) hwf hr hs (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hfp' hok1.nodeleg hok1.warm hok1.pre hok1.fork run
  -- t_1097_c22: the digest, `size / 2`, `h + 1` and the jump to the head
  have hF : (Nat.toB256 (928 + 96 * h + 96)).toNat = 928 + 96 * h + 96 :=
    toNat_toB256' (by omega)
  unfold t_1097_c22 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [hF, read_word hr' _ shaImg_digest, read_covered hs' (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := sz / 2)
    (by rw [show Bytes.toB256 [0x02] = (2 : B256) by decide]) (ri_div s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (h + 1))
    (by rw [show Bytes.toB256 [0x01] = Nat.toB256 1 by decide, toB256_add_toB256 (by omega),
      Nat.add_comm]) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨Gf, hr⟩ := ric_jumpCut (by simp only [List.mem_cons, List.not_mem_nil, or_false]) run
  refine ⟨b', M', Gf, Keep.of_sha hpost, ⟨hwf', by rw [hs']; omega, _, hr', ?_, by simp only [List.not_mem_nil,
    IsEmpty.forall_iff, implies_true]⟩, hr⟩
  rw [shaImg_out (by omega), packImg_word64 (by omega)]
  congr 2
  omega

end Blanc.Lift.BeaconDeposit
