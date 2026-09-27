import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.WalkSteps
import Blanc.Lift.Vyper
import Blanc.AddressSlotProofs
import Blanc.LidoCircuitBreakerRegistryModel
import Blanc.Lift.Weth9.Words

/-! Inversion of the deployed CircuitBreaker removal entry on a successful run. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

/-- Entry 32 first tests the canonical, nonzero target and enters its body.
The returned run retains the exact caller stack, memory, and residual gas.
The new-pauser argument is threaded through untouched: the guard never reads
it, so this holds for an arbitrary `newPauser`. -/
theorem entry32_target_guard_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {newPauser target : B256} {base : List B256} {post : Devm}
    (htarget : nonzeroCanonicalAddress target)
    (run : SFunc.Run prog sevm
      (St b (newPauser :: target :: 3 :: 0x3c2 :: base) M G)
      t_0934_c32 (.returned post)) :
    ∃ G', SFunc.RunCut prog sevm []
      (St b (newPauser :: target :: 3 :: 0x3c2 :: base) M G')
      t_0981_c32 (.done (.returned post)) := by
  have run := run.cut
  unfold t_0934_c32 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G6, run⟩ | ⟨hnz, G6, run⟩
  · have hmask : target &&&
        Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = target := by
      rw [B256.and_comm, Weth9.ff20_and_word,
        B256.toAdr_toB256_of_lt htarget.2]
    exact (htarget.1 (hmask ▸ hz)).elim
  · exact ⟨G6, run⟩

/-- The found-target branch clears the assignment's low address field and
continues with the actual old pauser; the packed upper bits are retained.
Generalised to an arbitrary canonical `newPauser`: this same continuation is
shared by the found-nonzero and removal branches, which diverge only later
at entry 4's test of `newPauser`. -/
theorem entry32_assignment_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {newPauser target : B256} {base : List B256} {post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (htarget : canonicalAddress target) (hmem : Mem.Wf M)
    (halign : M.size % 32 = 0)
    (hnewPauser : canonicalAddress newPauser)
    (hold : addressSlotReadWord
      (b.getStorVal sevm.currentTarget (mapSlot target 3)) ≠ 0)
    (run : SFunc.RunCut prog sevm []
      (St b (newPauser :: target :: 3 :: 0x3c2 :: base) M G)
      t_0981_c32 (.done (.returned post))) :
    ∃ G', SFunc.RunCut prog sevm []
      (St (afterSstore sevm
        (afterSload sevm b (mapSlot target 3))
        (mapSlot target 3)
        (addressSlotWriteWord
          (b.getStorVal sevm.currentTarget (mapSlot target 3)) newPauser))
        (addressSlotReadWord
          (b.getStorVal sevm.currentTarget (mapSlot target 3)) ::
          newPauser :: target :: 3 :: 0x3c2 :: base)
        ((M.write 0 target.toBytes).write 32 (3 : B256).toBytes) G')
      t_09da_c32 (.done (.returned post)) := by
  unfold t_0981_c32 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := target) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_and s1
  have htargetMask : target &&& Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = target := by
    rw [B256.and_comm, Weth9.ff20_and_word,
      B256.toAdr_toB256_of_lt htarget]
  rw [htargetMask] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_dup (w := (3 : B256)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_mstore s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_swap (n := 0) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_keccak s1
  have hhash :
      ((((M.write 0 target.toBytes).write 32 (3 : B256).toBytes).read 0 64).1).keccak =
        mapSlot target 3 := by
    rw [Mem.read_two_word_writes_at hmem (Mem.reads_data M) 0 target 3]
    rfl
  have hsize1 : (M.write 0 target.toBytes).size % 32 = 0 := by
    rw [Mem.size_write_word_at]
    split_ifs
    · exact halign
    · decide
  have hsize2 : ((M.write 0 target.toBytes).write 32 (3 : B256).toBytes).size % 32 = 0 := by
    rw [Mem.size_write_word_at]
    split_ifs
    · exact hsize1
    · decide
  have hsize64 : 64 ≤ ((M.write 0 target.toBytes).write 32 (3 : B256).toBytes).size := by
    rw [Mem.size_write_word_at]
    split_ifs with h
    · exact h
    · decide
  have hnoext :
      (((M.write 0 target.toBytes).write 32 (3 : B256).toBytes).read 0 64).2 =
        (M.write 0 target.toBytes).write 32 (3 : B256).toBytes :=
    Mem.read_snd_eq_self (memExtSize_of_le hsize2 (by omega))
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl,
    hhash, hnoext] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_dup (w := mapSlot target 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_dup (w := newPauser) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_dup (w := Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_and s1
  have hnewMask : Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
      newPauser = newPauser := by
    rw [Weth9.ff20_and_word, B256.toAdr_toB256_of_lt hnewPauser]
  rw [hnewMask] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_push s1
  have hhigh : Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00] = addressMask := by decide
  rw [hhigh] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_dup
    (w := b.getStorVal sevm.currentTarget (mapSlot target 3)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_and s1
  have hcomm :
      b.getStorVal sevm.currentTarget (mapSlot target 3) &&& addressMask =
      addressMask &&& b.getStorVal sevm.currentTarget (mapSlot target 3) :=
    B256.and_comm _ _
  rw [hcomm] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_swap (n := 1) rfl s1
  dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_and s1
  have haddr : b.getStorVal sevm.currentTarget (mapSlot target 3) &&& Bytes.toB256
      [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
       0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] =
      addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) := by
    rw [B256.and_comm, Weth9.ff20_eq]
    rfl
  rw [haddr] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_dup
    (w := addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3))) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_iszero s1
  have hflag : B256.eqCheck
      (addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3))) 0 = 0 := by
    simp [B256.eqCheck, hold]
  rw [hflag] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G33, run⟩ | ⟨hnz, G33, run⟩
  · exact ⟨G33, run⟩
  · exact (hnz rfl).elim

end Blanc.Lift.LidoCircuitBreakerDeployed
