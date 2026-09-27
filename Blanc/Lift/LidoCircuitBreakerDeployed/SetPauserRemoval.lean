import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserNonzero
import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryEffects

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
  simp only [show (Bytes.toB256 [64] : B256) = 64 from rfl,
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
  simp only [show (Bytes.toB256 [64] : B256) = 64 from rfl,
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

/-- The contract storage the removal arm (`t_0ada_c4` through `t_0bdc_c4`)
leaves, as a function of the storage `s` it starts from: every read value is
the bytecode's own read of `s` or of an earlier write. -/
def removalTailStor (s : Stor) (target : B256) : Stor :=
  let idx := s.get (mapSlot target 4)
  let last := addressSlotReadWord (s.get (registryArrayBase + (s.get 5 - 1)))
  let hole := registryArrayBase + (idx - 1)
  let s4 := (s.set hole (addressSlotWriteWord (s.get hole) last)).set (mapSlot last 4) idx
  let tk := ffWord + (s4.get 5 + registryArrayBase)
  ((s4.set tk (addressMask &&& s4.get tk)).set 5 (s4.get 5 + ffWord)).set (mapSlot target 4) 0

/-- The removal arm, from entry 4's zero-new-pauser test to entry 5's return:
the run returns to `base` with the `PauserSet` log and contract storage
`removalTailStor`. -/
theorem removalArm_inv {oldP target R : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (htarget : canonicalAddress target)
    (hold : canonicalAddress oldP)
    (hlast : canonicalAddress (addressSlotReadWord ((Devm.getStor b sevm.currentTarget).get
      (registryArrayBase + (b.getStorVal sevm.currentTarget 5 - 1)))))
    (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (run : SFunc.RunCut prog sevm []
      (St b (oldP :: 0 :: target :: 3 :: R :: base) M G)
      t_0ada_c4 (.done (.returned post))) :
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat),
      post = St (b'.addLog
        ⟨sevm.currentTarget, [pauserSetTopic, target, oldP, 0], data⟩) base M' G' ∧
      StorStep sevm b b' (removalTailStor (Devm.getStor b sevm.currentTarget) target) := by
  have hzero : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  obtain ⟨-, -, hwf1, hal1⟩ := scratch_mapSlot hmem halign target 4
  obtain ⟨b3, G3, h3, run⟩ := t0ada_inv hfork htarget hmem halign run
  obtain ⟨-, -, hwf2, hal2⟩ := scratch_word hwf1 hal1 5
  obtain ⟨b4, G4, h4, run⟩ := t0b27_inv hfork hwf1 hal1 run
  rw [h3.getStorVal] at run
  obtain ⟨-, -, hwf2', hal2'⟩ := scratch_word hwf2 hal2 5
  obtain ⟨-, -, hwf3, hal3⟩ := scratch_mapSlot hwf2' hal2'
    (addressSlotReadWord ((Devm.getStor b sevm.currentTarget).get
      (registryArrayBase + (b.getStorVal sevm.currentTarget 5 - 1)))) 4
  obtain ⟨b5, G5, h5, -, run⟩ := t0b6a_inv hfork hlast hwf2 hal2 run
  simp only [h4.getStorVal, h4.self, h3.self] at h5 run
  obtain ⟨b6, G6, h6, run⟩ := t0bdc_inv hfork htarget hwf3 hal3 run
  simp only [h5.getStorVal, h5.self] at h6
  obtain ⟨data, M', G7, rfl⟩ := entry5_inv hold hzero htarget run
  exact ⟨b6, data, M', G7, rfl, (h3.trans h4).trans (h5.trans h6)⟩

/-- The found-target prefix shared by the nonzero and removal branches: the
target guard, the assignment rewrite, and the old pauser's count decrement,
up to entry 4, with the world effect named. -/
theorem foundPrefix_inv {newPauser target oldP : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (htarget : nonzeroCanonicalAddress target) (hnew : canonicalAddress newPauser)
    (hold : nonzeroCanonicalAddress oldP)
    (hassign : addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) = oldP)
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: 3 :: 0x3c2 :: base) M G)
      t_0934_c32 (.returned post)) :
    ∃ b2 M2 G2, StorStep sevm b b2
        ((((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
          (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3))
            newPauser))).set (mapSlot oldP 6)
          (ffWord + ((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
            (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3))
              newPauser)).get (mapSlot oldP 6))) ∧
      Mem.Wf M2 ∧ M2.size % 32 = 0 ∧
      SFunc.RunCut prog sevm [] (St b2 (oldP :: newPauser :: target :: 3 :: 0x3c2 :: base) M2 G2)
        t_0a81_c4 (.done (.returned post)) := by
  obtain ⟨G1, run⟩ := entry32_target_guard_inv htarget run
  obtain ⟨G2, run⟩ := entry32_assignment_inv hfork htarget.2 hmem halign hnew
    (by rw [hassign]; exact hold.1) run
  rw [hassign] at run
  obtain ⟨-, -, hwf1, hal1⟩ := scratch_mapSlot hmem halign target 3
  obtain ⟨-, G3, run⟩ := t09da_inv hfork hold.2 hwf1 hal1 run
  obtain ⟨-, -, hwf2, hal2⟩ := scratch_mapSlot hwf1 hal1 oldP 6
  refine ⟨_, _, G3, ?_, hwf2, hal2, run⟩
  have h1 := ((StorStep.refl sevm b).sload (mapSlot target 3)).sstore (mapSlot target 3)
    (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) newPauser)
  have h2 := (h1.sload (mapSlot oldP 6)).sstore (mapSlot oldP 6)
    (ffWord + (afterSstore sevm (afterSload sevm b (mapSlot target 3)) (mapSlot target 3)
      (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3))
        newPauser)).getStorVal sevm.currentTarget (mapSlot oldP 6))
  exact h2.congr (by rw [h1.getStorVal])

end Blocks

/-! ## The removal branch's storage, against `rawRemovalPost` -/

/-- The tail slot the pop clears: `ff..ff + (L + base)` is the zero-based
slot `L - 1`. -/
theorem ffWord_add_length_base {L : Nat} (hpos : 0 < L) (hlt : L < 2 ^ 256) :
    ffWord + (Nat.toB256 L + registryArrayBase) = registryArraySlot (L - 1) := by
  unfold registryArraySlot
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_add, B256.toNat_add, B256.toNat_toB256_of_lt hlt,
    B256.toNat_toB256_of_lt (by omega : L - 1 < 2 ^ 256),
    show ffWord.toNat = 2 ^ 256 - 1 from by decide]
  unfold Nat.lo
  rw [Nat.add_mod_mod]
  have := B256.toNat_lt registryArrayBase
  rw [show 2 ^ 256 - 1 + (L + registryArrayBase.toNat) =
    (registryArrayBase.toNat + (L - 1)) + 2 ^ 256 by omega, Nat.add_mod_right]

theorem arrayEntrySlot_ne_arrayLengthSlot {i : Nat} (hi : i + 1 < 2 ^ 252) :
    arrayEntrySlot (Nat.toB256 (i + 1)) ≠ arrayLengthSlot := by
  intro heq
  have hb256 : i + 1 < 2 ^ 256 := by omega
  have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hb256]
    exact hi
  have hzero : (0 : B256).toNat < 2 ^ 252 := by
    rw [B256.toNat_zero]
    norm_num
  have hpayload : Nat.toB256 (i + 1) = 0 :=
    slot_injective_payload (region := arrayRegion) (by norm_num [arrayRegion]) hb hzero heq
  have hn := congrArg B256.toNat hpayload
  rw [B256.toNat_toB256_of_lt hb256] at hn
  simp only [B256.toNat_zero] at hn
  omega

/-- The storage the bytecode's removal arm leaves, started from the
found-target prefix's two writes, is exactly `rawRemovalPost`.  Every read
the bytecode performs is identified from the witness, and every raw slot
separation it needs comes from the branch's own `RegistryKeysFaithful`. -/
theorem removalTailStor_eq_rawRemovalPost
    {raw : Stor} {entries : List LidoCircuitBreaker.Entry} {target oldPauser : B256}
    {index : Nat}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index)) :
    removalTailStor
      ((raw.set (mapSlot target 3) (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)).set
        (mapSlot oldPauser 6) (Nat.toB256 (assignmentCount entries oldPauser - 1))) target =
      rawRemovalPost raw entries target oldPauser index ∧
    addressSlotReadWord
      (((raw.set (mapSlot target 3) (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)).set
        (mapSlot oldPauser 6) (Nat.toB256 (assignmentCount entries oldPauser - 1))).get
        (registryArrayBase +
          (((raw.set (mapSlot target 3) (addressSlotWriteWord (raw.get (mapSlot target 3)) 0)).set
            (mapSlot oldPauser 6) (Nat.toB256 (assignmentCount entries oldPauser - 1))).get 5 - 1))) =
      sourceLastTarget entries := by
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hfoundLt := findEntry_index_lt hfind
  have hlenLt := hw.entries_length_lt_2pow252
  obtain ⟨lastE, hlastE⟩ := last_some_of_findEntry hfind
  have hlastValid : nonzeroCanonicalAddress lastE.1 :=
    hw.targetsValid lastE (last_mem_of_last entries hlastE)
  have hsrc : sourceLastTarget entries = lastE.1 := by
    simp [sourceLastTarget, hlastE]
  have hm : nonzeroCanonicalAddress (sourceLastTarget entries) := hsrc ▸ hlastValid
  -- Witness reads of the pre-state.
  have hidx : raw.get (mapSlot target 4) = Nat.toB256 (index + 1) := by
    have h := hw.indices target htarget.2
    rw [solRegistryStorage_index _ _ htarget.2, findEntry_oneBasedIndexAt hfind] at h
    exact h
  have hlen : raw.get 5 = Nat.toB256 entries.length := by
    have h := hw.lengthWord
    rw [solRegistryStorage_length] at h
    exact h
  have htailRead : addressSlotReadWord (raw.get (registryArraySlot (entries.length - 1))) =
      sourceLastTarget entries := by
    have h := hw.arrayWords (entries.length - 1) (by omega)
    rw [solRegistryStorage_array _ _ (by omega)] at h
    rw [h, targetAt_last_of_last entries hlastE, hsrc]
  -- Raw slot separations from the faithful premise.
  have htailKey : solKey (arrayEntrySlot (Nat.toB256 entries.length)) =
      registryArraySlot (entries.length - 1) := by
    have h := solKey_arrayEntrySlot (index := entries.length - 1) (by omega)
    rwa [show entries.length - 1 + 1 = entries.length by omega] at h
  have hLb : (Nat.toB256 entries.length).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt (by omega)]
    exact hlenLt
  have hmemLen : arrayLengthSlot ∈ removalWriteKeys entries target oldPauser index := by
    simp [removalWriteKeys]
  have hmemIdx : indexSlot target ∈ removalWriteKeys entries target oldPauser index := by
    simp [removalWriteKeys]
  have hmemTail : arrayEntrySlot (Nat.toB256 entries.length) ∈
      removalWriteKeys entries target oldPauser index := by
    simp [removalWriteKeys]
  have hobsA : RegistryObservable entries.length (assignmentSlot target) :=
    Or.inl ⟨target, htarget.2, rfl⟩
  have hobsC : RegistryObservable entries.length (countSlot oldPauser) :=
    Or.inr (Or.inr (Or.inl ⟨oldPauser, hold.2, rfl⟩))
  have h5k3 : mapSlot target 3 ≠ 5 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen hobsA
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2).1
  have h5c6 : mapSlot oldPauser 6 ≠ 5 := by
    rw [← solKey_countSlot hold.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen hobsC
      (registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2).2.2
  have hk4k3 : mapSlot target 3 ≠ mapSlot target 4 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_indexSlot htarget.2]
    exact solKey_ne_of_faithful hfaithful hmemIdx hobsA
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hold.2).1
  have hk4c6 : mapSlot oldPauser 6 ≠ mapSlot target 4 := by
    rw [← solKey_countSlot hold.2, ← solKey_indexSlot htarget.2]
    exact solKey_ne_of_faithful hfaithful hmemIdx hobsC
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hold.2).2.2.symm
  have htk3 : mapSlot target 3 ≠ registryArraySlot (entries.length - 1) := by
    rw [← solKey_assignmentSlot htarget.2, ← htailKey]
    exact solKey_ne_of_faithful hfaithful hmemTail hobsA
      (registryAddressFamilies_ne_arrayEntrySlot htarget.2 hold.2 hLb).1
  have htc6 : mapSlot oldPauser 6 ≠ registryArraySlot (entries.length - 1) := by
    rw [← solKey_countSlot hold.2, ← htailKey]
    exact solKey_ne_of_faithful hfaithful hmemTail hobsC
      (registryAddressFamilies_ne_arrayEntrySlot htarget.2 hold.2 hLb).2.2
  have h5hole : registryArraySlot index ≠ 5 := by
    have hk := solKey_arrayEntrySlot (index := index) (by omega)
    rw [← hk, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨index, hfoundLt, rfl⟩))))
      (arrayEntrySlot_ne_arrayLengthSlot (by omega))
  have h5mk : mapSlot (sourceLastTarget entries) 4 ≠ 5 := by
    rw [← solKey_indexSlot hm.2, ← solKey_arrayLengthSlot]
    exact solKey_ne_of_faithful hfaithful hmemLen
      (Or.inr (Or.inl ⟨_, hm.2, rfl⟩))
      (registryAddressFamilies_ne_arrayLengthSlot hm.2 hold.2).2.1
  -- The bytecode's reads, rewritten.
  have hpredLen : Nat.toB256 entries.length - 1 = Nat.toB256 (entries.length - 1) :=
    (natToB256_pred_eq_sub_one _ (by omega) (by omega)).symm
  have hpredIdx : Nat.toB256 (index + 1) - 1 = Nat.toB256 index := by
    simpa using (natToB256_pred_eq_sub_one (index + 1) (by omega) (by omega)).symm
  have hnewLen : Nat.toB256 entries.length + ffWord = Nat.toB256 (entries.length - 1) := by
    rw [B256.add_comm, ffWord_add_natToB256 (by omega) (by omega)]
  have hRA : ∀ i, registryArraySlot i = registryArrayBase + Nat.toB256 i := fun _ => rfl
  have htail' := ffWord_add_length_base (by omega : 0 < entries.length)
    (by omega : entries.length < 2 ^ 256)
  simp only [hRA] at htc6 htk3 h5hole htailRead htail'
  refine ⟨?_, ?_⟩
  swap
  · simp only [Stor.get_set_ne _ h5c6, Stor.get_set_ne _ h5k3, hlen, hpredLen,
      Stor.get_set_ne _ htc6, Stor.get_set_ne _ htk3, htailRead]
  simp only [removalTailStor, rawRemovalPost, hRA, Stor.get_set_ne _ hk4c6,
    Stor.get_set_ne _ hk4k3, Stor.get_set_ne _ h5c6, Stor.get_set_ne _ h5k3,
    Stor.get_set_ne _ htc6, Stor.get_set_ne _ htk3, Stor.get_set_ne _ h5mk,
    Stor.get_set_ne _ h5hole, hidx, hlen, hpredLen, hpredIdx, htailRead, htail', hnewLen,
    addressSlotWriteWord, B256.or_zero']


/-! ## The found-target removal branch -/

/-- Every successful run of `setPauser` (entry 32) on a found target with a
zero new pauser returns to its caller's `base` stack, having emitted the
`PauserSet` log, with the contract's storage pointwise equal to
`rawRemovalPost` (the tail clear is the bytecode's masked clear, which
`rawRemovalPost`'s `addressSlotWriteWord _ 0` already states) and every other
account's storage unchanged.  Covers the last-index and non-last-index
removals alike: the bytecode does not branch on them. -/
theorem setPauser_removal_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index))
    (run : SFunc.Run prog sevm (St b (0 :: target :: 3 :: 0x3c2 :: base) M G)
      t_0934_c32 (.returned post)) :
    (∀ key, (Devm.getStor post sevm.currentTarget).get key =
      (rawRemovalPost (Devm.getStor b sevm.currentTarget) entries target oldPauser
        index).get key) ∧
    (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor b a) ∧
    ∃ (b' : Devm) (data : Bytes) (M' : Mem) (G' : Nat), post = St (b'.addLog
      ⟨sevm.currentTarget, [pauserSetTopic, target, oldPauser, 0], data⟩) base M' G' ∧
      b'.logs = b.logs := by
  have hzero : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hassign : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) = oldPauser := by
    have h := hw.assignments target htarget.2
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_assignmentAt hfind] at h
    exact h
  have hcountOld : (Devm.getStor b sevm.currentTarget).get (mapSlot oldPauser 6) =
      Nat.toB256 (assignmentCount entries oldPauser) := by
    have h := hw.counts oldPauser hold.2
    rw [solRegistryStorage_count _ _ hold.2] at h
    exact h
  have hk3c6 : mapSlot target 3 ≠ mapSlot oldPauser 6 := by
    rw [← solKey_assignmentSlot htarget.2, ← solKey_countSlot hold.2]
    exact solKey_ne_of_faithful hfaithful (by simp [removalWriteKeys])
      (Or.inl ⟨target, htarget.2, rfl⟩)
      (registryAddressFamilies_pairwise htarget.2 htarget.2 hold.2).2.1
  have hdec : ffWord + ((Devm.getStor b sevm.currentTarget).set (mapSlot target 3)
      (addressSlotWriteWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) 0)).get
        (mapSlot oldPauser 6) = Nat.toB256 (assignmentCount entries oldPauser - 1) := by
    rw [Stor.get_set_ne _ hk3c6, hcountOld,
      ffWord_add_natToB256 (assignmentCount_pos_of_findEntry hfind)
        (hw.assignmentCount_lt_2pow256 oldPauser)]
  obtain ⟨b2, M2, G2, h2, hwf2, hal2, run⟩ :=
    foundPrefix_inv hfork hmem halign htarget hzero hold hassign run
  rw [hdec] at h2
  rcases entry4_inv hzero run with ⟨hne, -⟩ | ⟨-, G4, run⟩
  · exact absurd rfl hne
  obtain ⟨hEq, hlastEq⟩ := removalTailStor_eq_rawRemovalPost hw htarget hfind hfaithful
  have hlast : canonicalAddress (addressSlotReadWord ((Devm.getStor b2 sevm.currentTarget).get
      (registryArrayBase + (b2.getStorVal sevm.currentTarget 5 - 1)))) := by
    rw [h2.getStorVal, h2.self]
    obtain ⟨lastE, hlastE⟩ := last_some_of_findEntry hfind
    have hv : nonzeroCanonicalAddress lastE.1 :=
      hw.targetsValid lastE (last_mem_of_last entries hlastE)
    have hc : canonicalAddress (sourceLastTarget entries) := by
      simpa [sourceLastTarget, hlastE] using hv.2
    exact (congrArg canonicalAddress hlastEq).mpr hc
  obtain ⟨b', data, M', G', rfl, h6⟩ :=
    removalArm_inv hfork htarget.2 hold.2 hlast hwf2 hal2 run
  have h := h2.trans h6
  rw [h2.self] at h
  refine ⟨fun key => ?_, fun a ha => ?_, b', data, M', G', rfl, h.logs⟩
  · rw [getStor_St_addLog, h.self]
    exact congrArg (fun s => Stor.get s key) hEq
  · rw [getStor_St_addLog, h.other a ha]

end Blanc.Lift.LidoCircuitBreakerDeployed
