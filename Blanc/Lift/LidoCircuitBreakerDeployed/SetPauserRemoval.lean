import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserNonzero

/-! Inversion of `Registry.setPauser`'s swap-and-pop removal arm (entry 4's
zero-new-pauser block `t_0ada_c4` through `t_0bdc_c4`) on the exact deployed
CircuitBreaker bytecode, and the found-target removal branch built on it. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

section Blocks

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}

/-- `t_0ada_c4` through `t_0b17_c4`: read the removed target's one-based
index and the array length, subtract one from the length through entry 25,
and pass the (always-true on success) bound check against the length. -/
theorem t0ada_inv {oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (htarget : canonicalAddress target)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0ada_c4 (.done (.returned post))) :
    ∃ b' G', StorStep sevm b b' (Devm.getStor b sevm.currentTarget) ∧
      SFunc.RunCut prog sevm []
        (St b' ((b.getStorVal sevm.currentTarget 5 - 1) :: 5 :: 0 ::
            b.getStorVal sevm.currentTarget (mapSlot target 4) ::
            oldP :: newP :: target :: 3 :: R :: base)
          ((M.write 0 target.toBytes).write 32 (4 : B256).toBytes) G')
        t_0b27_c4 (.done (.returned post)) := by
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hmem halign target 4
  unfold t_0ada_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  rw [mask_and_canonical htarget] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_dup (w := Bytes.toB256 [1]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [1] = 4 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_add s1
  rw [show (3 : B256) + Bytes.toB256 [2] = 5 from rfl] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_sload hfork s1
  rw [getStorVal_afterSload] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_swap (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨G33, ⟨D, callee, run⟩ | ⟨D, -, hr⟩⟩ := ric_call entry25_lookup run
  swap
  · cases hr
  obtain ⟨-, G34, rfl⟩ := entry25_returned_inv callee
  unfold t_0b17_c4 at run
  obtain ⟨G35, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_dup (w := b.getStorVal sevm.currentTarget 5 - Bytes.toB256 [1])
    (by simp [getStorVal_afterSload]) s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G41, run⟩ | ⟨_, G41, run⟩
  · unfold t_0b20_c4 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G42, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G43, rfl⟩ := ri_push s1
    obtain ⟨G44, run⟩ := ric_jump (List.not_mem_nil) entry26_lookup run
    exact (panic26_not_run run).elim
  · refine ⟨_, G41, ?_, run⟩
    exact (((StorStep.refl sevm b).sload _).sload _).sload _

theorem hiMask_eq : Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00] = addressMask := by decide

theorem ff20_and_eq_read (w : B256) :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& w =
      addressSlotReadWord w := by
  rw [Weth9.ff20_eq]
  rfl

/-- `t_0b27_c4` through `t_0b5a_c4`: read the array's last element (as an
address), subtract one from the removed one-based index through entry 25, and
pass the (always-true on success) bound check. -/
theorem t0b27_inv {L1 idx oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (L1 :: 5 :: 0 :: idx :: oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0b27_c4 (.done (.returned post))) :
    ∃ b' G', StorStep sevm b b' (Devm.getStor b sevm.currentTarget) ∧
      SFunc.RunCut prog sevm []
        (St b' ((idx - 1) :: 5 ::
            addressSlotReadWord (b.getStorVal sevm.currentTarget (registryArrayBase + L1)) ::
            addressSlotReadWord (b.getStorVal sevm.currentTarget (registryArrayBase + L1)) ::
            idx :: oldP :: newP :: target :: 3 :: R :: base)
          (M.write 0 (5 : B256).toBytes) G')
        t_0b6a_c4 (.done (.returned post)) := by
  obtain ⟨hkb, hnoext0, -, -⟩ := scratch_word hmem halign 5
  unfold t_0b27_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    hkb, hnoext0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_and s1
  rw [ff20_and_eq_read] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := addressSlotReadWord
    (b.getStorVal sevm.currentTarget ((5 : B256).toBytes.keccak + L1))) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_add s1
  rw [show (3 : B256) + Bytes.toB256 [2] = 5 from rfl] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_dup (w := idx) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨G24, ⟨D, callee, run⟩ | ⟨D, -, hr⟩⟩ := ric_call entry25_lookup run
  swap
  · cases hr
  obtain ⟨-, G25, rfl⟩ := entry25_returned_inv callee
  unfold t_0b5a_c4 at run
  obtain ⟨G26, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_dup (w := idx - Bytes.toB256 [1]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G32, run⟩ | ⟨_, G32, run⟩
  · unfold t_0b63_c4 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G33, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G34, rfl⟩ := ri_push s1
    obtain ⟨G35, run⟩ := ric_jump (List.not_mem_nil) entry27_lookup run
    exact (panic27_not_run run).elim
  · refine ⟨_, G32, ?_, run⟩
    exact ((StorStep.refl sevm b).sload _).sload _

/-- `t_0b6a_c4`: move the last element into the hole (keeping the hole's
upper 96 bits), record its new one-based index, re-read the length and pass
the nonempty check before the pop. -/
theorem t0b6a_inv {I1 last idx oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hlast : canonicalAddress last)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (I1 :: 5 :: last :: last :: idx :: oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0b6a_c4 (.done (.returned post))) :
    ∃ b' G', StorStep sevm b b'
        (((Devm.getStor b sevm.currentTarget).set (registryArrayBase + I1)
          (addressSlotWriteWord
            (b.getStorVal sevm.currentTarget (registryArrayBase + I1)) last)).set
          (mapSlot last 4) idx) ∧
      (((Devm.getStor b sevm.currentTarget).set (registryArrayBase + I1)
          (addressSlotWriteWord
            (b.getStorVal sevm.currentTarget (registryArrayBase + I1)) last)).set
          (mapSlot last 4) idx).get 5 ≠ 0 ∧
      SFunc.RunCut prog sevm []
        (St b' ((((Devm.getStor b sevm.currentTarget).set (registryArrayBase + I1)
          (addressSlotWriteWord
            (b.getStorVal sevm.currentTarget (registryArrayBase + I1)) last)).set
          (mapSlot last 4) idx).get 5 :: 5 :: last :: idx :: oldP :: newP :: target :: 3 ::
            R :: base)
          (((M.write 0 (5 : B256).toBytes).write 0 last.toBytes).write 32 (4 : B256).toBytes) G')
        t_0bdc_c4 (.done (.returned post)) := by
  obtain ⟨hkb, hnoext0, hwf5, hal5⟩ := scratch_word hmem halign 5
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hwf5 hal5 last 4
  unfold t_0b6a_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 [32]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    hkb, hnoext0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := (5 : B256).toBytes.keccak + I1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_and s1
  rw [hiMask_eq] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (n := 4) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_dup (w := Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_and s1
  rw [ff20_and_canonical hlast] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_or s1
  rw [B256.or_comm' last] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_dup (w := last) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_and s1
  rw [mask_and_canonical hlast] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_dup (w := (0 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [1] = 4 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl, hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_dup (w := idx) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G42, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G43, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G44, rfl⟩ := ri_add s1
  rw [show (3 : B256) + Bytes.toB256 [2] = 5 from rfl] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G45, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G46, rfl⟩ := ri_sload hfork s1
  have hstep := ((((StorStep.refl sevm b).sload ((5 : B256).toBytes.keccak + I1)).sstore
    ((5 : B256).toBytes.keccak + I1) (addressMask &&&
      b.getStorVal sevm.currentTarget ((5 : B256).toBytes.keccak + I1) ||| last)).sstore
    (mapSlot last 4) idx)
  rw [hstep.getStorVal] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G47, rfl⟩ := ri_dup (w := _) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G48, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G49, run⟩ | ⟨hnz, G49, run⟩
  · unfold t_0bd5_c4 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G50, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G51, rfl⟩ := ri_push s1
    obtain ⟨G52, run⟩ := ric_jump (List.not_mem_nil) entry28_lookup run
    exact (panic28_not_run run).elim
  · exact ⟨_, G49, hstep.sload 5, hnz, run⟩

/-- `t_0bdc_c4`: clear the tail slot's address field (a masked clear keeping
the upper 96 bits), store the decremented length, zero the removed target's
index, and fall through to entry 5. -/
theorem t0bdc_inv {lenC last idx oldP newP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (htarget : canonicalAddress target)
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (lenC :: 5 :: last :: idx :: oldP :: newP :: target :: 3 :: R :: base) M G)
      t_0bdc_c4 (.done (.returned post))) :
    ∃ b' G', StorStep sevm b b'
        ((((Devm.getStor b sevm.currentTarget).set (ffWord + (lenC + registryArrayBase))
          (addressMask &&&
            b.getStorVal sevm.currentTarget (ffWord + (lenC + registryArrayBase)))).set
          5 (lenC + ffWord)).set (mapSlot target 4) 0) ∧
      SFunc.RunCut prog sevm []
        (St b' (oldP :: newP :: target :: 3 :: R :: base)
          (((M.write 0 (5 : B256).toBytes).write 0 target.toBytes).write 32 (4 : B256).toBytes) G')
        t_0c5e_c5 (.done (.returned post)) := by
  obtain ⟨hkb, hnoext0, hwf5, hal5⟩ := scratch_word hmem halign 5
  obtain ⟨hhash, hnoext, -, -⟩ := scratch_mapSlot hwf5 hal5 target 4
  unfold t_0bdc_c4 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := (5 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 [32]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := Bytes.toB256 []) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    hkb, hnoext0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_dup (w := lenC) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_dup (w := ffWord) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_dup (w := ffWord + (lenC + (5 : B256).toBytes.keccak)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_and s1
  rw [hiMask_eq] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_swap (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_and s1
  rw [mask_and_canonical htarget] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_dup (w := (0 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_dup (w := (0 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_keccak s1
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (3 : B256) + Bytes.toB256 [1] = 4 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl, hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G42, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G43, rfl⟩ := ri_pop s1
  refine ⟨_, G43, ?_, run⟩
  exact (((((StorStep.refl sevm b).sload _).sstore _ _).sstore _ _).sstore _ _)

end Blocks

end Blanc.Lift.LidoCircuitBreakerDeployed
