import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.InvWalk

/-!
# Safety segment L2: the storing pass and the return, inverted
(converse of `body_insertLive`, as a cut run at the loop head)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeInsertLive
/-- **Inversion of the storing pass (`t_0f6e_c23` cut at entry 23).**  From the loop head at a
height `h ≤ 32` with `size` odd, every successful cut run passes the head test (so `h < 32`),
stores the node at `solBranchSlot h` and returns through entry 21.

Proof sketch.  `cases` along `body_insertLive`'s proof (about 40 nodes, no memory access); the
head test's failing arm is `POP; undefined`; the bounds check's failing arm `t_0f90_c23` is
`undefined`; the `SSTORE`'s successor is `afterSstore`; `.jump 21` is not cut; `.ret` gives the
`.done (.returned …)`. -/
theorem safe_insertLive {sevm : Sevm} {b : Devm}
    {sz nd x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256} {h G : Nat} {M : Mem}
    {r : Seg}
    (hfork : CoveredFork sevm.benvStat.fork) (hh : h ≤ 32) (hsz : sz.toNat % 2 = 1)
    (run : SFunc.RunCut prog sevm [23]
      (St b (Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ ::
        y₆ :: y₇ :: d :: rest) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' G', Keep (afterSstore sevm b (solBranchSlot h) nd) b' ∧
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
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_sstore hfork s1
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
