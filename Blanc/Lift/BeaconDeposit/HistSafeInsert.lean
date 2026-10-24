import Blanc.Lift.BeaconDeposit.HistSafeWorld
import Blanc.Lift.BeaconDeposit.SafeInsertDead
import Blanc.Lift.BeaconDeposit.SafeInsertLive

/-!
# Safety segments L1/L2 over a historical frame: the insertion loop's two passes, inverted

`safe_insertDead` over `ShaReadyH` (its `SLOAD` by `ri_sloadH`, its packed SHA site by
`ric_pack_shaH`) and `safe_insertLive` with its `SSTORE` by `ri_sstoreH`; the successors are
`afterSloadH`/`afterSstoreH`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- **Inversion of a dead pass (`t_0f6e_c23` cut at entry 23) over a historical frame.**  From the loop head at a height
`h ≤ 32` with `size` even, every successful cut run passes the head test (so `h < 32`) and ends
at the next head, one height up, with the combined node.

Proof sketch.  `cases` along `body_insertDead`'s walk with `SFunc.RunCutP` in place of `Run`
(the same constructors; `.jump 23` is `jumpCut`, the only way to `.at`; `.jump 22` is followed).
The head test `h < 32` has `t_10a9_c23 = POP; undefined` as its failing arm (no rule).  The bit
test is decided by `hsz` (`Nat.and_one_is_mod` through `B256.toNat_and`, as in
`body_insertLive`).  The precompile block as in segment B3's sketch; the `SLOAD` of
`Nat.toB256 h + 0 = solBranchSlot h` has successor `afterSloadH`. -/
theorem safe_insertDeadH {sevm : Sevm} {b : Devm} {sz nd : B256} {R : List B256} {h G : Nat}
    {M : Mem} {r : Seg}
    (hsha : ShaReadyH sevm b) (hh : h ≤ 32) (hsz : sz.toNat % 2 = 0) (hR : R.length ≤ 16)
    (hM : BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) [])
    (run : SFunc.RunCut prog sevm [23] (St b (Nat.toB256 h :: sz :: nd :: R) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' M' G', Keep (afterSloadH sevm b (solBranchSlot h)) b' ∧
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
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sloadH hsha.bal s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  set b1 := afterSloadH sevm b (solBranchSlot h) with hb1
  have hok1 : ShaReadyH sevm b1 := ⟨by rw [hb1, afterSloadH_getCode]; exact hsha.nodeleg,
    by rw [hb1, afterSloadH_accessedAddresses]; exact hsha.warm, hsha.pre, hsha.sg, hsha.bal⟩
  set br := b.getStorVal sevm.currentTarget (solBranchSlot h) with hbr
  have hfp' : img.sliceD 64 32 0 = (Nat.toB256 (928 + 96 * h)).toBytes := hfp
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_pack_shaH (a := br) (bw := nd)
    (n := 1024 + 96 * h) (f := 928 + 96 * h)
    (show prog[22]? = some (mcpyTree 0x10 0x25 0x0f 0xe8 22
      (mergeTree (shaCallTree 0x10 0x82 0x10 0x97 t_1079_c22 t_1093_c22 t_1097_c22))) from rfl)
    (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, not_false_eq_true]) (by decide) hwf hr hs (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hfp' hok1.nodeleg hok1.warm hok1.pre hok1.sg run
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

/-- **Inversion of the storing pass (`t_0f6e_c23` cut at entry 23) over a historical frame.**  From the loop head at a
height `h ≤ 32` with `size` odd, every successful cut run passes the head test (so `h < 32`),
stores the node at `solBranchSlot h` and returns through entry 21.

Proof sketch.  `cases` along `body_insertLive`'s proof (about 40 nodes, no memory access); the
head test's failing arm is `POP; undefined`; the bounds check's failing arm `t_0f90_c23` is
`undefined`; the `SSTORE`'s successor is `afterSstoreH`; `.jump 21` is not cut; `.ret` gives the
`.done (.returned …)`. -/
theorem safe_insertLiveH {sevm : Sevm} {b : Devm}
    {sz nd x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256} {h G : Nat} {M : Mem}
    {r : Seg}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) (hh : h ≤ 32) (hsz : sz.toNat % 2 = 1)
    (run : SFunc.RunCut prog sevm [23]
      (St b (Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ ::
        y₆ :: y₇ :: d :: rest) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' G', Keep (afterSstoreH sevm b (solBranchSlot h) nd) b' ∧
      r = .done (.returned (St b' rest M G')) := by
  have hhv : (Nat.toB256 h).toNat = h := B256.toNat_toB256_of_lt (by omega)
  have hbit : (Bytes.toB256 [0x01] &&& sz) = 1 := by
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
  rw [hlt] at run
  rcases ric_branch run with ⟨-, G7, run⟩ | ⟨hw, -⟩
  swap; · exact absurd hw (by decide)
  -- t_0f78_c23: the bit test
  unfold t_0f78_c23 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := sz) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  rw [hbit, show B256.eqCheck (Bytes.toB256 [0x01]) 1 = 1 by decide,
    show B256.eqCheck (1 : B256) 0 = 0 by decide] at run
  rcases ric_branch run with ⟨-, G15, run⟩ | ⟨hw, -⟩
  swap; · exact absurd hw (by decide)
  -- t_0f84_c23: the bounds check
  unfold t_0f84_c23 at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup (w := nd) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := Nat.toB256 h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_dup (w := Nat.toB256 h) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  rw [hlt] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G23, run⟩
  · exact absurd hw (by decide)
  -- t_0f91_c23: the store and the pops
  unfold t_0f91_c23 at run
  obtain ⟨G24, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add s1
  have hkey : Nat.toB256 h + Bytes.toB256 [0x00] = solBranchSlot h := by
    apply B256.toNat_inj
    rw [B256.toNat_add, hhv, show (Bytes.toB256 [0x00]).toNat = 0 from rfl, Nat.add_zero,
      Nat.lo_eq_of_lt (by omega)]
    exact (B256.toNat_toB256_of_lt (by omega)).symm
  rw [hkey] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_sstoreH hsg hbal s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_swap (n := 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_pop s1
  obtain ⟨G36, run⟩ := ric_jump (k := 21) (by decide) rfl run
  unfold t_10ac_c21 at run
  obtain ⟨G37, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_pop s1
  obtain ⟨Gf, hr⟩ := ric_ret run
  exact ⟨_, Gf, Keep.refl _, hr⟩

end Blanc.Lift.BeaconDeposit
