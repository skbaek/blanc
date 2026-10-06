import Blanc.AddressSlotProofs
import Blanc.Lift.UniswapV2Pair.WriterArithmetic
import Blanc.Lift.WalkSteps
import Blanc.Lift.ExactWalkSolc

/-! The literal repeated factory initializer and its two packed address writes. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def initializeLoaded0 (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b 6
def initializeWord0 (sevm : Sevm) (b : Devm) (token0 : Adr) : B256 :=
  addressSlotWriteWord (b.getStorVal sevm.currentTarget 6) token0.toB256
def initializeStored0 (sevm : Sevm) (b : Devm) (token0 : Adr) : Devm :=
  afterSstore sevm (initializeLoaded0 sevm b) 6 (initializeWord0 sevm b token0)
def initializeLoaded1 (sevm : Sevm) (b : Devm) (token0 : Adr) : Devm :=
  afterSload sevm (initializeStored0 sevm b token0) 7
def initializeWord1 (sevm : Sevm) (b : Devm) (token0 token1 : Adr) : B256 :=
  addressSlotWriteWord ((initializeStored0 sevm b token0).getStorVal sevm.currentTarget 7) token1.toB256
def initializeWritesBase (sevm : Sevm) (b : Devm) (token0 token1 : Adr) : Devm :=
  afterSstore sevm (initializeLoaded1 sevm b token0) 7 (initializeWord1 sevm b token0 token1)

/-- Exact execution of the actual two-write suffix, with both incoming store sentries. -/
theorem initializeWrites_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load0 store0 load1 store1 : Nat} {token0 token1 : Adr} {ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (cost0 : load0 = sloadCost sevm b 6)
    (costS0 : store0 = sstoreCost sevm (initializeLoaded0 sevm b) 6 (initializeWord0 sevm b token0))
    (cost1 : load1 = sloadCost sevm (initializeStored0 sevm b token0) 7)
    (costS1 : store1 = sstoreCost sevm (initializeLoaded1 sevm b token0) 7
      (initializeWord1 sevm b token0 token1))
    (sentry0 : gCallStipend < G + store0 + load1 + store1 + 38)
    (sentry1 : gCallStipend < G + store1 + 8)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1016) :
    SFunc.RunExact fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M
      (G + load0 + store0 + load1 + store1 + 78)) t_0fb2_c45
      (.returned (St (initializeWritesBase sevm b token0 token1) R M G)) := by
  unfold t_0fb2_c45
  refine rx_dest ?_
  refine rx_push (w := 6) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  rw [show G + load0 + store0 + load1 + store1 + 71 =
      (G + store0 + load1 + store1 + 71) + load0 from by omega]
  refine rx_sload_selC fork cost0 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 3) rfl ?_
  dsimp only [List.set]
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := token0.toB256) (addressSlotReadWord_toB256 token0)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := addressMask) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_and rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_or (v := initializeWord0 sevm b token0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  rw [show G + store0 + load1 + store1 + 38 =
      (G + load1 + store1 + 38) + store0 from by omega]
  refine rx_sstoreC fork costS0 (by omega) nonstatic ?_
  refine rx_push (w := 7) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  rw [show G + load1 + store1 + 32 = (G + store1 + 32) + load1 from by omega]
  refine rx_sload_selC fork cost1 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_swap (n := 3) rfl ?_
  dsimp only [List.set]
  refine rx_and (v := token1.toB256) (addressSlotReadWord_toB256 token1)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_and (v := addressMask &&& (initializeStored0 sevm b token0).getStorVal sevm.currentTarget 7)
    (B256.and_comm _ _) (by simp only [List.length_cons]; omega) ?_
  refine rx_or (v := initializeWord1 sevm b token0 token1) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  rw [show G + store1 + 8 = (G + 8) + store1 from by omega]
  refine rx_sstoreC fork costS1 (by omega) nonstatic ?_
  exact rx_ret

/-- Any successful literal packed suffix derives nonstatic and its complete returned state. -/
theorem initializeWrites_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {token0 token1 : Adr} {ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M G) t_0fb2_c45 o) :
    sevm.isStatic = false ∧ ∃ residual,
      o = .returned (St (initializeWritesBase sevm b token0 token1) R M residual) := by
  have h := run.cut
  unfold t_0fb2_c45 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rw [ff20_eq] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  rw [show (~~~ addressMask) &&& token0.toB256 = token0.toB256 from
    addressSlotReadWord_toB256 token0] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  change SFunc.RunCut fs sevm [] (St (afterSload sevm b 6)
    (addressMask :: token0.toB256 :: b.getStorVal sevm.currentTarget 6 :: 6 :: token1.toB256 ::
      (~~~ addressMask) :: ρ :: R) M _) _ _ at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  rw [show (~~~ addressMask) &&& token1.toB256 = token1.toB256 from
    addressSlotReadWord_toB256 token1] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  change SFunc.RunCut fs sevm [] (St (initializeLoaded1 sevm b token0)
    (((initializeStored0 sevm b token0).getStorVal sevm.currentTarget 7 &&& addressMask) ::
      token1.toB256 :: 7 :: ρ :: R) M _) _ _ at h
  rw [B256.and_comm ((initializeStored0 sevm b token0).getStorVal sevm.currentTarget 7) addressMask] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨residual, done⟩ := ric_ret h
  exact ⟨nonstatic, residual, Seg.done.inj done⟩

def initializeFactoryBase (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b 5
def initializeCoreBase (sevm : Sevm) (b : Devm) (token0 token1 : Adr) : Devm :=
  initializeWritesBase sevm (initializeFactoryBase sevm b) token0 token1

/-- Actual factory comparison followed by the sequential selected storage charges. -/
theorem initialize45_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G factoryLoad load0 store0 load1 store1 : Nat}
    {token0 token1 : Adr} {ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr)
    (factoryCost : factoryLoad = sloadCost sevm b 5)
    (cost0 : load0 = sloadCost sevm (initializeFactoryBase sevm b) 6)
    (costS0 : store0 = sstoreCost sevm (initializeLoaded0 sevm (initializeFactoryBase sevm b)) 6
      (initializeWord0 sevm (initializeFactoryBase sevm b) token0))
    (cost1 : load1 = sloadCost sevm (initializeStored0 sevm (initializeFactoryBase sevm b) token0) 7)
    (costS1 : store1 = sstoreCost sevm (initializeLoaded1 sevm (initializeFactoryBase sevm b) token0) 7
      (initializeWord1 sevm (initializeFactoryBase sevm b) token0 token1))
    (sentry0 : gCallStipend < G + store0 + load1 + store1 + 38)
    (sentry1 : gCallStipend < G + store1 + 8)
    (nonstatic : sevm.isStatic = false) (room : R.length ≤ 1016) :
    SFunc.RunExact fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M
      (G + factoryLoad + load0 + store0 + load1 + store1 + 106)) t_0f2c_c45
      (.returned (St (initializeCoreBase sevm b token0 token1) R M G)) := by
  unfold t_0f2c_c45
  refine rx_dest ?_
  refine rx_push (w := 5) rfl (by simp only [List.length_cons]; omega) ?_
  rw [show G + factoryLoad + load0 + store0 + load1 + store1 + 102 =
    (G + load0 + store0 + load1 + store1 + 102) + factoryLoad from by omega]
  refine rx_sload_selC fork factoryCost (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := (b.getStorVal sevm.currentTarget 5).toAdr.toB256)
    (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons]; omega) ?_
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_eq (v := 1) ?_ (by simp only [List.length_cons]; omega) ?_
  · rw [authorized]; exact ite_eq_left rfl
  refine rx_push (w := 0x0fb2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
  exact initializeWrites_exact fork cost0 costS0 cost1 costS1 sentry0 sentry1 nonstatic room

/-- Success derives the factory guard; arbitrary old token words and lock values are permitted. -/
theorem initialize45_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {token0 token1 : Adr} {ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (token1.toB256 :: token0.toB256 :: ρ :: R) M G) t_0f2c_c45 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr ∧ sevm.isStatic = false ∧
      ∃ residual, o = .returned (St (initializeCoreBase sevm b token0 token1) R M residual) := by
  have h := run.cut
  unfold t_0f2c_c45 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rw [show Bytes.toB256 [5] = (5 : B256) from rfl] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rw [ff20_eq] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_and hd
  rw [show (~~~ addressMask) &&& b.getStorVal sevm.currentTarget 5 =
    (b.getStorVal sevm.currentTarget 5).toAdr.toB256 from
    addressSlotReadWord_eq_toAdr_toB256 _] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · exact (bad.false_of_noOk (by decide : t_0f4c_c45.noOk = true)).elim
  · have same : sevm.caller.toB256 = (b.getStorVal sevm.currentTarget 5).toAdr.toB256 := by
      by_contra different
      exact nonzero (ite_eq_right different)
    have authorized : sevm.caller = (b.getStorVal sevm.currentTarget 5).toAdr := by
      simpa only [toAdr_toB256] using congrArg B256.toAdr same
    obtain ⟨nonstatic, residual, done⟩ := initializeWrites_inv fork h.uncut
    exact ⟨authorized, nonstatic, residual, done⟩

end Blanc.Lift.UniswapV2Pair
