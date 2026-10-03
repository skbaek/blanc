import Blanc.Lift.UniswapV2Pair.MintSource
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesCore
import Blanc.Lift.UniswapV2Pair.BalanceCallWalk
import Blanc.Lift.UniswapV2Pair.WriterLockStorage
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! Literal public mint entry, retaining the original instruction derivation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual mint lock test also creates the liquidity temporary. -/
theorem mintLockGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: ρ :: R) M G) t_1011_c41 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (afterSload sevm b 12) (0 :: toWord :: ρ :: R) M gas) t_1084_c41 seg := by
  unfold t_1011_c41 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, body⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_101e_c41.noOk = true))
  · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
    have unlocked : b.getStorVal sevm.currentTarget 12 = 1 := by
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact False.elim (accepted rfl)
    exact ⟨unlocked, gas, body⟩

/-- The lock test costs26 gas besides the selected slot12 read. -/
theorem mintLockGuard_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1008)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (charge : load = sloadCost sevm b 12)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (0 :: toWord :: ρ :: R) M G) t_1084_c41 o) :
    SFunc.RunExact cert.prog sevm (St b (toWord :: ρ :: R) M (G + load + 26))
      t_1011_c41 o := by
  unfold t_1011_c41
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 19 = (G + 19) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq (v := 1) (by rw [unlocked]; decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1084) rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- The actual lock write and packed reserve read preceding the token calls. -/
def mintLockedWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 12) 12 0

/-- The first mint internal call caches all three packed reserve fields. -/
theorem mintReservePrefix_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: ρ :: R) M G) t_1011_c41 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧ ∃ gas,
      let locked := mintLockedWorld sevm b
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (afterSload sevm locked 8)
          (reserveTimestampRead (locked.getStorVal sevm.currentTarget 8) ::
           reserve1Read (locked.getStorVal sevm.currentTarget 8) ::
           reserve0Read (locked.getStorVal sevm.currentTarget 8) ::
           0 :: 0 :: 0 :: toWord :: ρ :: R) M gas) t_1094_c41 seg := by
  obtain ⟨unlocked, _, run⟩ := mintLockGuard_inv fork run
  unfold t_1084_c41 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  have nonstatic := ri_sstore_nonstatic fork (StepIn.toRun hs)
  obtain ⟨_, rfl⟩ := ri_sstore fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  cases run with
  | callHalt d hk pop callee =>
      rw [show cert.prog[56]? = some t_0d90_c56 from rfl] at hk
      cases hk
      have callee' := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, impossible⟩ := reserves_callee_inv fork (callee'.mono StepIn.toRun)
      cases impossible
  | callRet d hk pop callee body =>
      rw [show cert.prog[56]? = some t_0d90_c56 from rfl] at hk
      cases hk
      have callee' := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨gas, returned⟩ := reserves_callee_inv fork (callee'.mono StepIn.toRun)
      cases returned
      exact ⟨unlocked, nonstatic, gas, body⟩


/-- Selected lock-store and reserve-read costs compose with the real getter56. -/
theorem mintReservePrefix_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load lock reserve : Nat} {toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1008)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (nonstatic : sevm.isStatic = false)
    (loadEq : load = sloadCost sevm b 12)
    (lockEq : lock = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (reserveEq : reserve = sloadCost sevm (mintLockedWorld sevm b) 8)
    (sentry : gCallStipend < G + reserve + 87 + lock)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm (mintLockedWorld sevm b) 8)
        (reserveTimestampRead ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: 0 :: toWord :: ρ :: R) M G) t_1094_c41 o) :
    SFunc.RunExact cert.prog sevm
      (St b (toWord :: ρ :: R) M (G + reserve + 100 + lock + load + 26)) t_1011_c41 o := by
  apply mintLockGuard_exact fork room unlocked loadEq
  unfold t_1084_c41
  rw [show G + reserve + 100 + lock = (G + reserve + 87 + lock) + 13 by omega]
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap rfl
  apply rx_sstoreC fork lockEq sentry nonstatic
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1094) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x0d90) rfl (by simp only [List.length_cons]; omega)
  apply rx_callRet (show cert.prog[56]? = some t_0d90_c56 from rfl)
    (reserves_callee_exact fork reserveEq (by simp only [List.length_cons]; omega))
  exact body

/-- Literal first request and code guard derive the token0 target before its STATICCALL. -/
theorem mintFirstRequest_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {timestamp r1 r0 toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: toWord :: ρ :: R) M G)
      t_1094_c41 seg) :
    let token := (b.getStorVal sevm.currentTarget 6).toAdr.toB256
    let loaded := afterSload sevm b 6
    (loaded.getCode token.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (temporalAccountAccessBase loaded token.toAdr)
          (0 :: token :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
           token :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) gas) t_110e_c41 seg := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  unfold t_1094_c41 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, same0] at eq; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  have hp := of_run_address (StepIn.toRun hs)
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have eq := St.of_stackRel hp
  rw [stack] at eq
  rw [eq] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [B256.and_comm, ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_extcodesize fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, body⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_110a_c41.noOk = true))
  · have zero := eq_zero_of_iszero_ne_zero accepted
    change B256.eqCheck (((afterSload sevm b 6).getCode
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256.toAdr).size.toB256) 0 = 0 at zero
    have nonzero : ((afterSload sevm b 6).getCode
        (b.getStorVal sevm.currentTarget 6).toAdr.toB256.toAdr).size.toB256 ≠ 0 := by
      intro hz
      rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    refine ⟨nonzero, gas, ?_⟩
    simpa only [zero,
      show Bytes.toB256 [6] = (6 : B256) from rfl,
      show Bytes.toB256 [0] = (0 : B256) from rfl,
      show Bytes.toB256 [32] = (32 : B256) from rfl,
      show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
      show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
      show (128 : B256) + Bytes.toB256 [36] = 164 from by decide,
      balanceRequestMemory, balanceOfSelectorWord] using body


/-- The two literal balanceOf call sites in public mint. -/
inductive MintBalanceSite
  | first | second

def MintBalanceSite.callTree : MintBalanceSite → SFunc
  | .first => t_110e_c41
  | .second => t_11b1_c41

def MintBalanceSite.returnTree : MintBalanceSite → SFunc
  | .first => t_1122_c41
  | .second => t_11c5_c41

def MintBalanceSite.decodeTree : MintBalanceSite → SFunc
  | .first => t_1138_c41
  | .second => t_11db_c41

/-- Both actual call guards consume the shared provenance-preserving inversion. -/
theorem mintBalanceCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : MintBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M G)
      site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M callGas)
        (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) M 128 36 128 32 1 out ∧
      out.length < 2^256 ∧
      StaticAnswered sevm b token.toAdr (M.read 128 36).1 out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (0 :: a :: x :: y :: R)
          ((M.extends [(128, 36), (128, 32)]).write 128 (out.take 32)) tailGas)
        site.returnTree seg := by
  cases site
  · exact staticCallGuard_invP [0x11, 0x22] (by decide) rfl StepIn.toRun fork (by decide) run
  · exact staticCallGuard_invP [0x11, 0xc5] (by decide) rfl StepIn.toRun fork (by decide) run

/-- The width check concerns full returndata, not the physical32byte output. -/
theorem mintBalanceReturn_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {a x y z : B256} {seg : Seg} (site : MintBalanceSite)
    (mem : PtrMem 128 192 M) (bound : b.returnData.length < 2^256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (a :: x :: y :: z :: R) M G) site.returnTree seg) :
    32 ≤ b.returnData.length ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St b (b.returnData.length.toB256 :: 128 :: R) M gas) site.decodeTree seg := by
  cases site
  · exact returnWidthGuard_invP [0x11, 0x38] (by decide) rfl StepIn.toRun mem bound (by decide) run
  · exact returnWidthGuard_invP [0x11, 0xdb] (by decide) rfl StepIn.toRun mem bound (by decide) run

/-- Extract each actual observation with full answer and the original same-D continuation. -/
theorem mintBalanceObservation_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : MintBalanceSite)
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) G) site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      StepIn D sevm
        (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (balanceRequestMemory M sevm.currentTarget)
        128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm b token.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: R)
          (balanceReplyMemory M sevm.currentTarget out) tailGas) site.decodeTree seg := by
  obtain ⟨gw, callGas, d, out, _, call, post, bound, answered, tail⟩ :=
    mintBalanceCall_inv site fork run
  have full : d.returnData.length < 2^256 := by rw [post.returnData]; exact bound
  change SFunc.RunCutP (StepIn D) cert.prog sevm C
    (St d (0 :: a :: x :: y :: R) (balanceReplyMemory M sevm.currentTarget out) _) _ _ at tail
  obtain ⟨long, tailGas, decoded⟩ :=
    mintBalanceReturn_inv site (balanceReplyMemory_ptr out mem) full tail
  rw [post.returnData] at long decoded
  rw [balanceRequestMemory_read wf sevm.currentTarget] at answered
  exact ⟨gw, callGas, d, out, tailGas, call, post, long, bound, answered, decoded⟩

/-- The actual guards have5gas before the callee and64gas after it. -/
theorem mintBalanceObservation_exact {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {callGas decodeGas : Nat} {z token a x y : B256} {o : Outcome}
    (site : MintBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (room : R.length ≤ 1015)
    (call : Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: a :: x :: y :: R)
    (returnedGas : d.gasLeft = decodeGas + 64)
    (long : 32 ≤ d.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d (d.returnData.length.toB256 :: 128 :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) decodeGas) site.decodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) (callGas + 5)) site.callTree o := by
  have raw : Ninst.Run sevm
      (St b (callGas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d := by
    obtain ⟨xl, filled, step⟩ := call
    exact ⟨xl, filled, 0, step 0⟩
  have bound := ReturnDataBound.staticcall_returnData_length_lt raw fork
  have decoded : SFunc.RunExact cert.prog sevm
      (St d (0 :: a :: x :: y :: R)
        (balanceReplyMemory M sevm.currentTarget d.returnData) (decodeGas + 42))
      site.returnTree o := by
    cases site
    · exact returnWidthGuard_exact [0x11, 0x38] (by decide) (by decide) rfl
        (balanceReplyMemory_ptr d.returnData mem) (by omega) bound long body
    · exact returnWidthGuard_exact [0x11, 0xdb] (by decide) (by decide) rfl
        (balanceReplyMemory_ptr d.returnData mem) (by omega) bound long body
  have stackRoom : (a :: x :: y :: R).length ≤ 1018 := by simp only [List.length_cons]; omega
  cases site
  · exact staticCallGuard_exact [0x11, 0x22] (by decide) (by decide) rfl
      fork stackRoom call success (by omega) decoded
  · exact staticCallGuard_exact [0x11, 0xc5] (by decide) (by decide) rfl
      fork stackRoom call success (by omega) decoded


/-- The actual suffix after the balance word is loaded at each mint call site. -/
def MintBalanceSite.afterDecodeTree (site : MintBalanceSite) : SFunc :=
  match site.decodeTree with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

/-- The literal decoder reads only the physical output word while retaining full reply metadata. -/
theorem mintBalanceDecode_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {lengthWord : B256} {out : Bytes} {seg : Seg} (site : MintBalanceSite)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (long : 32 ≤ out.length)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (lengthWord :: 128 :: R) (balanceReplyMemory M sevm.currentTarget out) G)
      site.decodeTree seg) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget out) gas) site.afterDecodeTree seg := by
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape] at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨gas, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (128 : B256).toNat = 128 from rfl,
    balanceReplyMemory_word wf sevm.currentTarget out long,
    (balanceReplyMemory_ptr out mem).read_self (by decide : 128 + 32 ≤ 192)] at eq
  subst d
  exact ⟨gas, run⟩
/-- Literal second request and code guard derive the token1 target before its STATICCALL. -/
theorem mintSecondRequest_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {balance0 r1 r0 toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G)
      MintBalanceSite.first.afterDecodeTree seg) :
    let token := (b.getStorVal sevm.currentTarget 7).toAdr.toB256
    let loaded := afterSload sevm b 7
    (loaded.getCode token.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (temporalAccountAccessBase loaded token.toAdr)
          (0 :: token :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
           token :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) gas) t_11b1_c41 seg := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  change SFunc.RunCutP _ _ _ _ _ (.next (.push [7] _) _) _ at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, same0] at eq; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  have hp := of_run_address (StepIn.toRun hs)
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have eq := St.of_stackRel hp
  rw [stack] at eq
  rw [eq] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [B256.and_comm, ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_extcodesize fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, body⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_11ad_c41.noOk = true))
  · have zero := eq_zero_of_iszero_ne_zero accepted
    change B256.eqCheck (((afterSload sevm b 7).getCode
      (b.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256) 0 = 0 at zero
    have nonzero : ((afterSload sevm b 7).getCode
        (b.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0 := by
      intro hz
      rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    refine ⟨nonzero, gas, ?_⟩
    simpa only [zero,
      show Bytes.toB256 [7] = (7 : B256) from rfl,
      show Bytes.toB256 [0] = (0 : B256) from rfl,
      show Bytes.toB256 [32] = (32 : B256) from rfl,
      show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
      show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
      show (128 : B256) + Bytes.toB256 [36] = 164 from by decide,
      balanceRequestMemory, balanceOfSelectorWord] using body




/-- From the real locked mint entry, extract both token answers before checked amounts. -/
theorem mintBalancePrefix_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: ρ :: R) M G) t_1011_c41 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 : Nat),
      let locked := mintLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let token0 := (reserveWorld.getStorVal sevm.currentTarget 6).toAdr.toB256
      let u0 := afterSload sevm reserveWorld 6
      let w0 := temporalAccountAccessBase u0 token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (u0.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d0 (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M0 decodedGas0)
        MintBalanceSite.first.afterDecodeTree seg ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1
        (164 :: 0x70a08231 :: token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor locked a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        MintBalanceSite.second.afterDecodeTree seg := by
  obtain ⟨unlocked, nonstatic, _, reserves⟩ := mintReservePrefix_inv fork run
  obtain ⟨code0, _, firstCall⟩ := mintFirstRequest_inv fork mem reserves
  have request0 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  obtain ⟨gw0, callGas0, d0, out0, _, call0, post0, long0, bound0, answered0, decode0⟩ :=
    mintBalanceObservation_inv .first fork request0 mem.wf firstCall
  obtain ⟨decodedGas0, decoded0⟩ := mintBalanceDecode_inv .first request0 mem.wf long0 decode0
  have reply0 := balanceReplyMemory_ptr out0 request0
  obtain ⟨code1, _, secondCall⟩ := mintSecondRequest_inv fork reply0 decoded0
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget) :=
    balanceRequestMemory_ptr reply0 sevm.currentTarget
  obtain ⟨gw1, callGas1, d1, out1, _, call1, post1, long1, bound1, answered1, decode1⟩ :=
    mintBalanceObservation_inv .second fork request1 reply0.wf secondCall
  obtain ⟨decodedGas1, decoded1⟩ := mintBalanceDecode_inv .second request1 reply0.wf long1 decode1
  have stor0 : ∀ a, Devm.getStor d0 a = Devm.getStor (mintLockedWorld sevm b) a := by
    intro a
    refine (post0.stor a).trans ?_
    have warm : Devm.getStor
        (temporalAccountAccessBase (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6)
          ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr.toB256.toAdr) a =
        Devm.getStor (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6) a := by
      simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    rw [warm, afterSload_getStor, afterSload_getStor]
  have stor1 : ∀ a, Devm.getStor d1 a = Devm.getStor (mintLockedWorld sevm b) a := by
    intro a
    refine (post1.stor a).trans ?_
    have warm : Devm.getStor
        (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr) a =
        Devm.getStor (afterSload sevm d0 7) a := by
      simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    rw [warm, afterSload_getStor, stor0 a]
  have logs0 : d0.logs = b.logs := by
    refine post0.logs.trans ?_
    rw [temporalAccountAccessBase_logs, afterSload_logs, afterSload_logs,
      mintLockedWorld, afterSstore_logs, afterSload_logs]
  have logs1 : d1.logs = b.logs := by
    refine post1.logs.trans ?_
    rw [temporalAccountAccessBase_logs, afterSload_logs, logs0]
  have output0 : d0.output = b.output := by
    refine (post0.output rfl).trans ?_
    rw [temporalAccountAccessBase_output, afterSload_output, afterSload_output,
      mintLockedWorld, afterSstore_output, afterSload_output]
  have output1 : d1.output = b.output := by
    refine (post1.output rfl).trans ?_
    rw [temporalAccountAccessBase_output, afterSload_output, output0]
  exact ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, code0, call0, post0, long0, bound0,
    answered0, decoded0, code1, call1, post1, long1, bound1, answered1,
    stor0, stor1, logs1, output1, decoded1⟩

/-- The literal checked subtraction derives balance cover and retains the same-D continuation. -/
theorem mintAmount0_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound : r0.toNat < 2 ^ 112)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G) MintBalanceSite.second.afterDecodeTree seg) :
    r0 ≤ b0 ∧ ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b ((b0 - r0) :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M gas) t_1201_c41 seg := by
  unfold MintBalanceSite.afterDecodeTree MintBalanceSite.decodeTree t_11db_c41 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := b0) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show r0 &&& Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = r0 from feeReserveWord_eq bound] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256) from by decide] at run
  cases run with
  | callHalt d lookup pop callee =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
  | callRet d lookup pop callee body =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨cover, gas, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
      exact ⟨cover, gas, body⟩

/-- The literal checked subtraction derives balance cover and retains the same-D continuation. -/
theorem mintAmount1_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {amount0 b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (amount0 :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G) t_1201_c41 seg) :
    r1 ≤ b1 ∧ ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b ((b1 - r1) :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M gas) t_1225_c41 seg := by
  unfold t_1201_c41 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := b1) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show r1 &&& Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = r1 from feeReserveWord_eq bound] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256) from by decide] at run
  cases run with
  | callHalt d lookup pop callee =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
  | callRet d lookup pop callee body =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨cover, gas, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
      exact ⟨cover, gas, body⟩

/-- Both actual checked amounts precede the original fee68 caller. -/
theorem mintAmounts_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G)
      MintBalanceSite.second.afterDecodeTree seg) :
    r0 ≤ b0 ∧ r1 ≤ b1 ∧ ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b ((b1 - r1) :: 0 :: (b0 - r0) :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M gas)
      t_1225_c41 seg := by
  obtain ⟨cover0, _, run⟩ := mintAmount0_inv bound0 run
  obtain ⟨cover1, gas, run⟩ := mintAmount1_inv bound1 run
  exact ⟨cover0, cover1, gas, run⟩

/-- Extract the actual fee callee and its original1233 continuation before source freshness. -/
theorem mintFeeCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (amount1 :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G)
      t_1225_c41 seg) :
    ∃ feeGas feePost, SFunc.RunP (StepIn D) cert.prog sevm
      (St b (r1 :: r0 :: 0x1233 :: mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M feeGas)
      t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_1233_c41 seg := by
  unfold t_1225_c41 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  cases run with
  | callHalt d lookup pop callee =>
      change some t_26ec_c68 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, returned⟩ :=
        fee68_inv fork mem bound0 bound1 checked
      cases returned
  | callRet d lookup pop callee body =>
      change some t_26ec_c68 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      exact ⟨_, _, checked, body⟩

/-- Exact checked amount caller, including its literal masking and call59 charge. -/
theorem mintAmount0_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound : r0.toNat < 2 ^ 112) (cover : r0 ≤ b0) (room : R.length ≤ 1005)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b ((b0 - r0) :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G) t_1201_c41 seg) :
    SFunc.RunExactCut cert.prog sevm C (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (G + 94))
      MintBalanceSite.second.afterDecodeTree seg := by
  unfold MintBalanceSite.afterDecodeTree MintBalanceSite.decodeTree t_11db_c41
  apply rxc_swap (S' := 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) rfl
  apply rxc_pop
  apply rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x1201) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := b0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (v := r0) (feeReserveWord_eq bound) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_226e_c59) rfl
    (sub59_exact cover (by simp only [List.length_cons]; omega)) body

/-- Exact checked amount caller, including its literal masking and call59 charge. -/
theorem mintAmount1_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {amount0 b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound : r1.toNat < 2 ^ 112) (cover : r1 ≤ b1) (room : R.length ≤ 1005)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b ((b1 - r1) :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G) t_1225_c41 seg) :
    SFunc.RunExactCut cert.prog sevm C (St b (amount0 :: 0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (G + 95))
      t_1201_c41 seg := by
  unfold t_1201_c41
  apply rxc_dest
  apply rxc_swap (S' := 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) rfl
  apply rxc_pop
  apply rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x1225) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := b1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (v := r1) (feeReserveWord_eq bound) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega)
  apply rxc_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_226e_c59) rfl
    (sub59_exact cover (by simp only [List.length_cons]; omega)) body

/-- The two real subtraction calls cost189 gas and feed the original fee call. -/
theorem mintAmounts_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (cover0 : r0 ≤ b0) (cover1 : r1 ≤ b1) (room : R.length ≤ 1005)
    (body : SFunc.RunExactCut cert.prog sevm C
      (St b ((b1 - r1) :: 0 :: (b0 - r0) :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G)
      t_1225_c41 seg) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (G + 189))
      MintBalanceSite.second.afterDecodeTree seg := by
  rw [show G + 189 = (G + 95) + 94 from by omega]
  exact mintAmount0_exact bound0 cover0 room (mintAmount1_exact bound1 cover1 room body)

/-- Derive both amounts and the real fee call before applying finite recipient freshness. -/
theorem mintAmountsFee_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M G)
      MintBalanceSite.second.afterDecodeTree seg) :
    r0 ≤ b0 ∧ r1 ≤ b1 ∧ ∃ feeGas feePost,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (b1 - r1) (b0 - r0) b1 b0 r1 r0 toWord ρ R) M feeGas)
        t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_1233_c41 seg := by
  obtain ⟨cover0, cover1, _, run⟩ := mintAmounts_inv bound0 bound1 run
  obtain ⟨feeGas, feePost, callee, body⟩ := mintFeeCall_inv fork mem bound0 bound1 run
  exact ⟨cover0, cover1, feeGas, feePost, callee, body⟩

/-- Literal29gas fee caller transports a separately constructed actual fee run. -/
theorem mintFeeCall_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {feeGas : Nat} {feePost : Devm}
    {amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (room : R.length ≤ 1005)
    (callee : SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: 0x1233 :: mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M feeGas)
      t_26ec_c68 (.returned feePost))
    (body : SFunc.RunExactCut cert.prog sevm C feePost t_1233_c41 seg) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (amount1 :: 0 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        M (feeGas + 29)) t_1225_c41 seg := by
  unfold t_1225_c41
  apply rxc_dest
  apply rxc_swap rfl
  dsimp only [List.set]
  apply rxc_pop
  apply rxc_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x1233) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x26ec) rfl (by simp only [List.length_cons]; omega)
  exact rxc_callRet (g := t_26ec_c68) rfl callee body

/-- Both amounts and fee caller compose with218 literal gas before the fee callee. -/
theorem mintAmountsFee_exact {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {feeGas : Nat} {feePost : Devm}
    {b1 b0 r1 r0 toWord ρ : B256} {seg : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (cover0 : r0 ≤ b0) (cover1 : r1 ≤ b1) (room : R.length ≤ 1005)
    (callee : SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: 0x1233 ::
        mintFeeLocals (b1 - r1) (b0 - r0) b1 b0 r1 r0 toWord ρ R) M feeGas)
      t_26ec_c68 (.returned feePost))
    (body : SFunc.RunExactCut cert.prog sevm C feePost t_1233_c41 seg) :
    SFunc.RunExactCut cert.prog sevm C
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M (feeGas + 218))
      MintBalanceSite.second.afterDecodeTree seg := by
  rw [show feeGas + 218 = (feeGas + 29) + 189 from by omega]
  exact mintAmounts_exact bound0 bound1 cover0 cover1 room (mintFeeCall_exact room callee body)

/-- Actual1011 entry derives both token observations, checked amounts and the original fee continuation. -/
theorem mintCheckedFeePrefix_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: ρ :: R) M G) t_1011_c41 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 : Nat)
      (feeGas : Nat) (feePost : Devm),
      let locked := mintLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let token0 := (reserveWorld.getStorVal sevm.currentTarget 6).toAdr.toB256
      let u0 := afterSload sevm reserveWorld 6
      let w0 := temporalAccountAccessBase u0 token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (u0.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d0 (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M0 decodedGas0)
        MintBalanceSite.first.afterDecodeTree seg ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1
        (164 :: 0x70a08231 :: token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor locked a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        MintBalanceSite.second.afterDecodeTree seg ∧
      r0 ≤ balance0 ∧ r1 ≤ Bytes.toB256 (out1.take 32) ∧
      SFunc.RunP (StepIn D) cert.prog sevm
        (St d1 (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (Bytes.toB256 (out1.take 32) - r1) (balance0 - r0)
            (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ R)
          (balanceReplyMemory M0 sevm.currentTarget out1) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_1233_c41 seg := by
  obtain ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1⟩ := mintBalancePrefix_inv fork mem run
  have bound0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have bound1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have reply0 := balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr mem sevm.currentTarget)
  have reply1 := balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr reply0 sevm.currentTarget)
  obtain ⟨cover0, cover1, feeGas, feePost, feeRun, suffix⟩ :=
    mintAmountsFee_inv fork reply1 bound0 bound1 decoded1
  exact ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix⟩

/-- The actual selected factory observation and its finite-recipient source obligation. -/
def MintActualFeeSource (K : WriterKey → Prop) (st : State)
    (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (R : List B256)
    (M : Mem) (r1 r0 ρ : B256) (o : Outcome) : Prop :=
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes),
      StepIn D sevm
        (St (feeFactoryCallWorld sevm b)
          (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
            132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost (feeFactoryCallWorld sevm b) d
        (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
        (ExternalOperation.encode .feeTo) out ∧
      (FeeMintFresh K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1 →
        ∃ observed : FeeMintSourceObservation K st D sevm b R M r1 r0 ρ o,
          observed.d = d ∧ observed.out = out)

/-- First extract the actual factory reply; only that reply's recipient needs finite freshness. -/
theorem mintFee_observed_source_inv {K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunP (StepIn D) cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 o) :
    MintActualFeeSource K st D sevm b R M r1 r0 ρ o := by
  obtain ⟨code, gw, callGas, d, out, decodeGas, branchGas, gas,
    step, post, width, bound, answer, decoder, branch, guards, result⟩ :=
    fee68_inv fork mem bound0 bound1 run
  refine ⟨gw, callGas, d, out, step, post, width, bound, answer, ?_⟩
  intro fresh
  have postRep := rep.fee_factory_post post
  have last : feeKLastWord sevm d = st.kLast := by
    rcases postRep.fixed with ⟨_,_,_,_,_,_,_,_,_,_,last,_⟩
    change (d.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using last
  have sourceGuards : feeBranchAccepts sevm (feeKLastWorld sevm d) st.kLast
      (Bytes.toB256 (out.take 32)) r0 r1 := by rw [← last]; exact guards
  exact ⟨⟨code, gw, callGas, d, out, decodeGas, branchGas, gas,
    step, post, width, bound, answer, decoder, branch, guards, last, result,
    feeBranch_source_result postRep bound0 bound1 sourceGuards fresh⟩, rfl, rfl⟩

/-- The same lock effects used by the bytecode give the incoming fee's actual finite storage. -/
theorem WriterRep.mint_locked_world {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((mintLockedWorld sevm b).getStor sevm.currentTarget) { st with unlocked := 0 } := by
  rw [mintLockedWorld, afterSstore_getStor_self, afterSload_getStor]
  exact rep.mint_lock_store

/-- Actual1011 observations supply finite locked storage before any actual-recipient freshness premise. -/
theorem mintObservedFeePrefix_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {toWord ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: ρ :: R) M G) t_1011_c41 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 : Nat)
      (feeGas : Nat) (feePost : Devm),
      let locked := mintLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let token0 := (reserveWorld.getStorVal sevm.currentTarget 6).toAdr.toB256
      let u0 := afterSload sevm reserveWorld 6
      let w0 := temporalAccountAccessBase u0 token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (u0.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d0 (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M0 decodedGas0)
        MintBalanceSite.first.afterDecodeTree seg ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1
        (164 :: 0x70a08231 :: token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor locked a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        MintBalanceSite.second.afterDecodeTree seg ∧
      r0 ≤ balance0 ∧ r1 ≤ Bytes.toB256 (out1.take 32) ∧
      SFunc.RunP (StepIn D) cert.prog sevm
        (St d1 (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (Bytes.toB256 (out1.take 32) - r1) (balance0 - r0)
            (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ R)
          (balanceReplyMemory M0 sevm.currentTarget out1) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_1233_c41 seg ∧
      MintActualFeeSource K { st with unlocked := 0 } D sevm d1
        (mintFeeLocals (Bytes.toB256 (out1.take 32) - r1) (balance0 - r0)
          (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ R)
        (balanceReplyMemory M0 sevm.currentTarget out1) r1 r0 0x1233 (.returned feePost) := by
  obtain ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix⟩ :=
    mintCheckedFeePrefix_inv fork mem run
  have feeRep : WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } := by
    rw [stor1]
    exact rep.mint_locked_world
  have reply0 := balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr mem sevm.currentTarget)
  have reply1 := balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr reply0 sevm.currentTarget)
  have bound0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have bound1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have source := mintFee_observed_source_inv fork reply1 feeRep bound0 bound1 feeRun
  exact ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix, source⟩

/-- All actual fee branches retain the caller locals and the allocated pointer, including LP scratch writes. -/
theorem mintFeePost_machine {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {K w r0 r1 : B256} {G : Nat} (mem : PtrMem 128 192 M) :
    (feeBranchPost sevm b R M K w r0 r1 G).stack = feeOnWord w :: R ∧
    PtrMem 128 192 (feeBranchPost sevm b R M K w r0 r1 G).memory := by
  unfold feeBranchPost
  split
  · exact ⟨rfl, mem⟩
  · unfold feeOnPost
    split
    · exact ⟨rfl, mem⟩
    · split
      · unfold feeGrowthPost feeLiquidityPost
        split
        · exact ⟨rfl, mem⟩
        · exact ⟨rfl, lpMintMemory_ptr (lpMintScratch_ptr mem w) w _⟩
      · exact ⟨rfl, mem⟩

/-- The fee return flag agrees with the actual source fee result in all six branches. -/
theorem mintFeePost_flag {st : State} {sevm : Sevm} {b : Devm} {w r0 r1 : B256} :
    feeOnWord w = if (feeBranchSourceFee st sevm b w r0 r1).feeOn then 1 else 0 := by
  by_cases zero : w.toAdr = 0
  · have word : w.toAdr.toB256 = 0 := by rw [zero]; rfl
    rw [feeBranchSourceFee, ite_eq_left zero, feeOnWord, word]
    change B256.eqCheck (B256.eqCheck 0 0) 0 = 0
    decide
  · have word : w.toAdr.toB256 ≠ 0 := fun h => zero (Adr.toB256_inj h)
    have flag : feeOnWord w = 1 := by
      simp only [feeOnWord, B256.eqCheck, ite_eq_right word, ite_true]
    rw [flag, feeBranchSourceFee, ite_eq_right zero]
    split
    · rfl
    · split
      · unfold feeGrowthSourceFee
        split <;> rfl
      · rfl

/-- Consume the actual fee observation and suffix; cache, flag and memory bindings are derived. -/
theorem mintFee_source_suffix_frame_inv {K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem}
    {amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (observation : FeeMintSourceObservation K st D sevm b
      (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M r1 r0 0x1233 (.returned feePost))
    (fresh : MintAfterFeeFresh
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1).state toWord)
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm [] feePost t_1233_c41 (.done o)) :
    MintAfterFeeFrameResult
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      frame (feeMintObserved toWord amount1 amount0 b1 b0 r1 r0 bound0 bound1)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      sevm feePost R amount1 amount0 b1 b0 toWord o := by
  have returned := observation.returned
  rw [observation.last] at returned
  have postEq := Outcome.returned.inj returned
  have rep : WriterRep
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      (feePost.getStor sevm.currentTarget)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1).state := by
    have storageEq := congrArg (fun world : Devm => world.getStor sevm.currentTarget) postEq
    exact storageEq.symm ▸ observation.sourceResult.2.1
  have machine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm observation.d)
    (R := mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R)
    (K := st.kLast) (w := Bytes.toB256 (observation.out.take 32))
    (r0 := r0) (r1 := r1) (G := observation.residual)
    (feeReplyMemory_ptr observation.out (feeRequestMemory_ptr mem))
  rw [← postEq] at machine
  have cache : MintAfterFeeCache
      (feeMintObserved toWord amount1 amount0 b1 b0 r1 r0 bound0 bound1)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1)
      (feeOnWord (Bytes.toB256 (observation.out.take 32))) amount1 amount0 b1 b0 r1 r0 toWord :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, mintFeePost_flag⟩
  have self := St.self (d := feePost) machine.1 rfl
  have raw : SFunc.Run cert.prog sevm
      (St feePost
        (feeOnWord (Bytes.toB256 (observation.out.take 32)) ::
          0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        feePost.memory feePost.gasLeft) t_1233_c41 o := by
    have original := (SFunc.runP_iff_runCutP_nil.mpr suffix).mono StepIn.toRun
    have transported := (congrArg (fun world : Devm => SFunc.Run cert.prog sevm world t_1233_c41 o) self).mp original
    simpa only [mintFeeLocals] using transported
  exact mintAfterFee_frame_inv fork machine.2 rep fresh cache time pair sender bound0 bound1 raw

/-- Two-stage actual recipient obligations retain the factory observation and complete suffix result. -/
def MintActualFeeFinished (K : WriterKey → Prop) (st : State)
    (D : Exec.Deriv) (sevm : Sevm) (b feePost : Devm) (R : List B256)
    (M : Mem) (amount1 amount0 b1 b0 r1 r0 toWord ρ : B256)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (frame : Frame) (o : Outcome) : Prop :=
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes),
      StepIn D sevm
        (St (feeFactoryCallWorld sevm b)
          (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
            132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: 0x1233 :: (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R))
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost (feeFactoryCallWorld sevm b) d
        (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: 0x1233 :: (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R))
        (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
        (ExternalOperation.encode .feeTo) out ∧
      (FeeMintFresh K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1 →
        ∃ observed : FeeMintSourceObservation K st D sevm b (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M r1 r0 0x1233 (.returned feePost),
          observed.d = d ∧ observed.out = out ∧
          (MintAfterFeeFresh
            (feeBranchSourceKeys K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1)
            (feeBranchSourceFee st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1).state toWord →
            MintAfterFeeFrameResult
              (feeBranchSourceKeys K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1)
              frame (feeMintObserved toWord amount1 amount0 b1 b0 r1 r0 bound0 bound1)
              (feeBranchSourceFee st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1)
              sevm feePost R amount1 amount0 b1 b0 toWord o))

theorem mintActualFeeFinished_inv {K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem}
    {amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (source : MintActualFeeSource K st D sevm b
      (mintFeeLocals amount1 amount0 b1 b0 r1 r0 toWord ρ R) M r1 r0 0x1233 (.returned feePost))
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm [] feePost t_1233_c41 (.done o)) :
    MintActualFeeFinished K st D sevm b feePost R M amount1 amount0 b1 b0 r1 r0 toWord ρ
      bound0 bound1 frame o := by
  obtain ⟨gw, callGas, d, out, step, post, width, bound, answer, source⟩ := source
  refine ⟨gw, callGas, d, out, step, post, width, bound, answer, ?_⟩
  intro fresh
  obtain ⟨observed, dEq, outEq⟩ := source fresh
  refine ⟨observed, dEq, outEq, ?_⟩
  intro recipientFresh
  have fresh' : MintAfterFeeFresh
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observed.d)
        (Bytes.toB256 (observed.out.take 32)) r0 r1)
      (feeBranchSourceFee st sevm (feeKLastWorld sevm observed.d)
        (Bytes.toB256 (observed.out.take 32)) r0 r1).state toWord := by
    simpa only [dEq, outEq] using recipientFresh
  have finished := mintFee_source_suffix_frame_inv fork mem bound0 bound1 observed fresh'
    frame time pair sender suffix
  simpa only [dEq, outEq] using finished

/-- Finite observations and conditional touched-recipient source result of the actual1011 run. -/
def MintSourcePrefixResult (K : WriterKey → Prop) (st : State) (D : Exec.Deriv)
    (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (toWord ρ : B256)
    (frame : Frame) (o : Outcome) : Prop :=
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 : Nat)
      (feeGas : Nat) (feePost : Devm),
      let locked := mintLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let token0 := (reserveWorld.getStorVal sevm.currentTarget 6).toAdr.toB256
      let u0 := afterSload sevm reserveWorld 6
      let w0 := temporalAccountAccessBase u0 token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (u0.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d0 (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M0 decodedGas0)
        MintBalanceSite.first.afterDecodeTree (.done o) ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1
        (164 :: 0x70a08231 :: token1 :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor locked a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d1 (Bytes.toB256 (out1.take 32) :: 0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        MintBalanceSite.second.afterDecodeTree (.done o) ∧
      r0 ≤ balance0 ∧ r1 ≤ Bytes.toB256 (out1.take 32) ∧
      SFunc.RunP (StepIn D) cert.prog sevm
        (St d1 (r1 :: r0 :: 0x1233 ::
          mintFeeLocals (Bytes.toB256 (out1.take 32) - r1) (balance0 - r0)
            (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ R)
          (balanceReplyMemory M0 sevm.currentTarget out1) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] feePost t_1233_c41 (.done o) ∧
      ∃ bound0 : r0.toNat < 2 ^ 112, ∃ bound1 : r1.toNat < 2 ^ 112,
        MintActualFeeFinished K { st with unlocked := 0 } D sevm d1 feePost R
          (balanceReplyMemory M0 sevm.currentTarget out1)
          (Bytes.toB256 (out1.take 32) - r1) (balance0 - r0)
          (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ bound0 bound1 frame o

/-- Complete actual1011 inverse to the finite mint suffix, with only actual touched-recipient obligations. -/
theorem mintSourcePrefix_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (toWord :: ρ :: R) M G) t_1011_c41 (.done o)) :
    MintSourcePrefixResult K st D sevm b R M toWord ρ frame o := by
  obtain ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix, source⟩ :=
    mintObservedFeePrefix_inv fork mem rep run
  have reply0 := balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr mem sevm.currentTarget)
  have reply1 := balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr reply0 sevm.currentTarget)
  have bound0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have bound1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have finished := mintActualFeeFinished_inv fork reply1 bound0 bound1 source frame time pair sender suffix
  exact ⟨unlocked, nonstatic, gw0, callGas0, d0, out0, decodedGas0,
    gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost, code0, call0, post0, long0, width0,
    answered0, decoded0, code1, call1, post1, long1, width1, answered1,
    stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix, bound0, bound1, finished⟩

/-- Mint's literal uint ABI return starts after the fully allocated mint suffix. -/
theorem mintUintReturn_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {v : B256} {o : Outcome} (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm (St b (v :: R) M G) t_039b_c86 o) :
    ∃ d, o = .halted d ∧ d.output = v.toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  exact getterWord_tail_ptr_inv mem (by simpa only [t_039b_c86, t_039b_c98] using run)

/-- Mint already allocated192 bytes, so the actual uint ABI return costs43 gas. -/
theorem mintUintReturn_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {v : B256} (mem : PtrMem 128 192 M) (room : R.length ≤ 1019) :
    SFunc.RunExact cert.prog sevm (St b (v :: R) M (G + 43)) t_039b_c86
      (.halted (getterWordPost b R M v G)) := by
  have charge : 43 + (calculateMemoryGasCost (memExtSize 192 128 32) -
      calculateMemoryGasCost 192) = 43 := by decide
  simpa only [Nat.add_assoc, charge, t_039b_c86, t_039b_c98] using
    getterWord_tail_ptr_exact mem room

/-- Literal mint calldata decoder preserves the actual same-D callee and return continuation. -/
theorem mintAbiCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel avail : B256} {o : Outcome}
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [avail, 4, 0x039b, sel] M G) t_047f_c86 (.done o)) :
    ∃ calleeGas calleePost,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b [(Sevm.dataWord sevm 4).toAdr.toB256, 0x039b, sel] M calleeGas)
        t_1011_c41 (.returned calleePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_039b_c86 (.done o) := by
  unfold t_047f_c86 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_val (w := (Sevm.dataWord sevm 4).toAdr.toB256)
    (ff20_and_word _) (ri_and (StepIn.toRun hs))
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  cases run with
  | callHalt d lookup pop callee =>
      change some t_1011_c41 = _ at lookup
      cases lookup
      exact False.elim (callee.not_halted_entry
        (S := [9,11,12,18,19,20,21,22,23,24,25,26,27,41,56,58,59,60,62,65,66,68,69,70,72,74])
        (by decide) (by decide : 41 ∈ [9,11,12,18,19,20,21,22,23,24,25,26,27,41,56,58,59,60,62,65,66,68,69,70,72,74])
        (by rfl : cert.prog[41]? = some t_1011_c41) rfl)
  | callRet d lookup pop callee body =>
      change some t_1011_c41 = _ at lookup
      cases lookup
      exact ⟨_, _, (St.of_pop1 pop).2 ▸ callee, body⟩

/-- Successful mint ABI entry derives its wrapped32-byte argument guard. -/
theorem mintAbiGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [sel] M G) t_0469_c86 (.done o)) :
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧
      ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St b [sevm.data.length.toB256 - 4, 4, 0x039b, sel] M gas)
        t_047f_c86 (.done o) := by
  unfold t_0469_c86 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, gas, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_047b_c86.noOk = true))
  · simp only [show Bytes.toB256 [4] = (4 : B256) from rfl,
      show Bytes.toB256 [32] = (32 : B256) from rfl] at accepted
    have guard : (32 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 32 = 1 := by
        simp only [B256.ltCheck, lt_of_not_ge ne, ite_true]
      rw [flag] at accepted
      exact accepted (by decide)
    exact ⟨guard, gas, run⟩

/-- Actual mint selector dispatch retains the supplied derivation into0469. -/
theorem mintSelector_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [] M G) t_001a_c0 (.done o)) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [0x6a627842] M gas) t_0469_c86 (.done o) := by
  unfold t_001a_c0 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_shr (StepIn.toRun hs)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x6a627842 : B256) from selector] at eq
  subst d
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x6a627842 : B256) = 0 from by decide,
    ite_true] at run
  unfold t_002b_c0 at run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0xba,0x9a,0x7a,0x56]) (0x6a627842 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0097_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x7e,0xce,0xbe,0x00]) (0x6a627842 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_00d3_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨gas, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_0469_c86) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x6a627842 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  exact ⟨gas, run⟩

/-- The literal decoder contributes23gas around the actual mint callee and its ABI return. -/
theorem mintAbiCall_exact {sevm : Sevm} {b post : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (callee : SFunc.RunExact cert.prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256, 0x039b, sel] M G) t_1011_c41 (.returned post))
    (tail : SFunc.RunExact cert.prog sevm post t_039b_c86 o) :
    SFunc.RunExact cert.prog sevm (St b [avail,4,0x039b,sel] M (G + 23)) t_047f_c86 o := by
  unfold t_047f_c86
  apply rx_dest
  apply rx_pop
  apply rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_and (v := (Sevm.dataWord sevm 4).toAdr.toB256) (ff20_and_word _) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x1011) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_callRet rfl callee tail

/-- Actual0469 argument guard costs40gas before its literal calldata decoder. -/
theorem mintAbiGuard_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (body : SFunc.RunExact cert.prog sevm
      (St b [sevm.data.length.toB256 - 4,4,0x039b,sel] M G) t_047f_c86 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + 40)) t_0469_c86 o := by
  unfold t_0469_c86
  apply rx_dest
  apply rx_push (w := 0x039b) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_sub' (v := sevm.data.length.toB256 - 4) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_lt (v := 0) (ltCheck_zero_of_le guard) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x047f) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body

/-- The complete public mint ABI wrapper exposes its real callee and original return. -/
theorem mintAbi_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b [sel] M G) t_0469_c86 (.done o)) :
    (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ ∃ calleeGas calleePost,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b [(Sevm.dataWord sevm 4).toAdr.toB256,0x039b,sel] M calleeGas)
        t_1011_c41 (.returned calleePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_039b_c86 (.done o) := by
  obtain ⟨guard,_,decoded⟩ := mintAbiGuard_inv run
  exact ⟨guard,mintAbiCall_inv decoded⟩

/-- Construct the complete literal ABI wrapper with63gas over its actual callee budget. -/
theorem mintAbi_exact {sevm : Sevm} {b post : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (callee : SFunc.RunExact cert.prog sevm
      (St b [(Sevm.dataWord sevm 4).toAdr.toB256,0x039b,sel] M G) t_1011_c41 (.returned post))
    (tail : SFunc.RunExact cert.prog sevm post t_039b_c86 o) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + 63)) t_0469_c86 o := by
  have body := mintAbiCall_exact (avail := sevm.data.length.toB256 - 4) callee tail
  have entry := mintAbiGuard_exact guard body
  simpa only [Nat.add_assoc,show (23 + 40 : Nat) = 63 from rfl] using entry

/-- ActualPC0 derives scratch memory, nonpayability, size and its same-D mint callee. -/
theorem mintPc0_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ ∃ calleeGas calleePost,
        SFunc.RunP (StepIn D) cert.prog sevm
          (St b [(Sevm.dataWord sevm 4).toAdr.toB256,0x039b,0x6a627842] getterInitMemory calleeGas)
          t_1011_c41 (.returned calleePost) ∧
        SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_039b_c86 (.done o) := by
  obtain ⟨value,size,_,selected⟩ := syncGuards_inv run
  obtain ⟨_,entry⟩ := mintSelector_inv selector (SFunc.runP_iff_runCutP_nil.mp selected)
  exact ⟨value,size,mintAbi_inv entry⟩

/-- ActualPC0 supplies the complete finite callee observations from its own entry memory. -/
theorem mintPc0_source_inv {K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ ∃ calleeGas calleePost,
        SFunc.RunP (StepIn D) cert.prog sevm
          (St b [(Sevm.dataWord sevm 4).toAdr.toB256,0x039b,0x6a627842] getterInitMemory calleeGas)
          t_1011_c41 (.returned calleePost) ∧
        MintSourcePrefixResult K st D sevm b [0x6a627842] getterInitMemory
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b frame (.returned calleePost) ∧
        SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_039b_c86 (.done o) := by
  obtain ⟨value,size,guard,gas,post,callee,tail⟩ := mintPc0_inv selector run
  have source := mintSourcePrefix_inv fork getterInitMemory_ptr rep frame time pair sender
    (SFunc.runP_iff_runCutP_nil.mp callee)
  exact ⟨value,size,guard,gas,post,callee,source,tail⟩

/-- Concrete rawPC0 execution supplies the same derivation used by every mint observation. -/
theorem mintBytecode_source_inv {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let D : Exec.Deriv := ⟨0,sevm,St b [] Mem.empty G,.ok post,run⟩
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ ∃ calleeGas calleePost,
        SFunc.RunP (StepIn D) cert.prog sevm
          (St b [(Sevm.dataWord sevm 4).toAdr.toB256,0x039b,0x6a627842] getterInitMemory calleeGas)
          t_1011_c41 (.returned calleePost) ∧
        MintSourcePrefixResult K st D sevm b [0x6a627842] getterInitMemory
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b frame (.returned calleePost) ∧
        SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_039b_c86 (.done (.halted post)) := by
  obtain ⟨f,entry,derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  exact mintPc0_source_inv fork rep frame time pair sender selector derived

/-- The literal mint PC0 guard and selector path costs165gas before0469. -/
theorem mintDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0x6a627842] getterInitMemory G) t_0469_c86 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 165)) t_0000_c0 o := by
  rw [show G + 165 = (G + 102) + 63 by omega]
  refine getterString_guards_exact value size ?_
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_shr (v := 0x6a627842) selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x0097) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_0097_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x7ecebe00) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x00d3) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_00d3_c0
  apply rx_dest
  exact cmp_hit (tgt := t_0469_c86) rfl rfl body

/-- Construct token0's actual request, selected load and code warming from the reserve cache. -/
theorem mintFirstRequest_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {timestamp r1 r0 toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M) (room : R.length ≤ 990)
    (code : ((afterSload sevm b 6).getCode (b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr)
        (0 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) G) t_110e_c41 o) :
    SFunc.RunExact cert.prog sevm
      (St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: toWord :: ρ :: R) M
        (G + sloadCost sevm b 6 +
          temporalAccountAccessCost (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr + 166))
      t_1094_c41 o := by
  let access := temporalAccountAccessCost (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr
  have mem1 : PtrMem 128 160 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  rw [show G + sloadCost sevm b 6 + access + 166 =
    (G + access + 160) + sloadCost sevm b 6 + 6 by omega]
  unfold t_1094_c41
  apply rx_dest
  apply rx_pop
  apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 9)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + access + 134) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack,List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St (afterSload sevm b 6)
      (sevm.currentTarget.toB256 :: 128 :: 64 :: b.getStorVal sevm.currentTarget 6 ::
        r1 :: r0 :: 0 :: 0 :: 0 :: toWord :: ρ :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + access + 134)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 6)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word (mem2.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_swap4
  apply rx_swap rfl
  change SFunc.RunExact cert.prog sevm
    (St (afterSload sevm b 6)
      (0 :: 128 :: b.getStorVal sevm.currentTarget 6 :: r1 :: 128 :: 0 :: r0 ::
        0 :: toWord :: ρ :: R) (balanceRequestMemory M sevm.currentTarget)
      (G + access + 107)) _ o
  apply rx_pop
  apply rx_swap2
  apply rx_swap4
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap2
  apply rx_and (v := (b.getStorVal sevm.currentTarget 6).toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 164) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap2
  apply rx_swap1
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  rw [show G + access + 22 = (G + 22) + access by omega]
  dsimp only [access]
  conv in temporalAccountAccessCost _ _ =>
    rw [← toAdr_toB256 (b.getStorVal sevm.currentTarget 6).toAdr]
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0)
    (by simp only [toAdr_toB256,B256.eqCheck,code,ite_false])
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x110e) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  simpa only [toAdr_toB256] using body

/-- Decode the physical reply word, retaining the complete returndata in the world. -/
theorem mintBalanceDecode_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {lengthWord : B256} {out : Bytes} {o : Outcome}
    (site : MintBalanceSite) (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (long : 32 ≤ out.length) (room : R.length ≤ 1022)
    (body : SFunc.RunExact cert.prog sevm
      (St b (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M sevm.currentTarget out) G) site.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (lengthWord :: 128 :: R) (balanceReplyMemory M sevm.currentTarget out) (G + 6))
      site.decodeTree o := by
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape]
  apply rx_dest
  apply rx_pop
  apply rx_mload (i := 128) (v := Bytes.toB256 (out.take 32)) (c := 3)
    (by rw [St.extCost_eq (balanceReplyMemory_ptr out mem).size]; decide)
    (balanceReplyMemory_word wf sevm.currentTarget out long)
    ((balanceReplyMemory_ptr out mem).read_self (by decide)) (by omega)
  exact body

/-- Construct token1's actual request, selected load and code warming from the reserve cache. -/
theorem mintSecondRequest_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {balance0 r1 r0 toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (room : R.length ≤ 990)
    (code : ((afterSload sevm b 7).getCode (b.getStorVal sevm.currentTarget 7).toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase (afterSload sevm b 7) (b.getStorVal sevm.currentTarget 7).toAdr)
        (0 :: (b.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          0 :: balance0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory M sevm.currentTarget) G) t_11b1_c41 o) :
    SFunc.RunExact cert.prog sevm
      (St b (balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M
        (G + sloadCost sevm b 7 +
          temporalAccountAccessCost (afterSload sevm b 7) (b.getStorVal sevm.currentTarget 7).toAdr + 149))
      MintBalanceSite.first.afterDecodeTree o := by
  let access := temporalAccountAccessCost (afterSload sevm b 7) (b.getStorVal sevm.currentTarget 7).toAdr
  have mem1 : PtrMem 128 192 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  rw [show G + sloadCost sevm b 7 + access + 149 =
    (G + access + 146) + sloadCost sevm b 7 + 3 by omega]
  change SFunc.RunExact _ _ _ (.next (.push [7] _) _) _
  apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
  apply rx_sload_selC fork rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + access + 126) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack,List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St (afterSload sevm b 7)
      (sevm.currentTarget.toB256 :: 128 :: 64 :: b.getStorVal sevm.currentTarget 7 ::
        balance0 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + access + 126)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 3)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word (mem2.read_self (by decide))
    (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap4
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap3
  apply rx_and (v := (b.getStorVal sevm.currentTarget 7).toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word _) (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 0x70a08231) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 164) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap2
  apply rx_swap1
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 36) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  rw [show G + access + 22 = (G + 22) + access by omega]
  dsimp only [access]
  conv in temporalAccountAccessCost _ _ =>
    rw [← toAdr_toB256 (b.getStorVal sevm.currentTarget 7).toAdr]
  apply rx_extcodesize fork (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0)
    (by simp only [toAdr_toB256,B256.eqCheck,code,ite_false])
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x11b1) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  simpa only [toAdr_toB256] using body

/-- Both actual token requests and full-reply guards compose before the amount checks.
Only the compiled calls, successful return metadata and downstream instruction continuation
are supplied here; the complete caller constructs that continuation from fee/pricing data. -/
theorem mintBalanceRequests_exact {sevm : Sevm} {b d0 d1 : Devm}
    {R : List B256} {M : Mem} {callGas0 callGas1 G : Nat}
    {timestamp r1 r0 toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (room : R.length ≤ 990)
    (code0 : ((afterSload sevm b 6).getCode (b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr)
        (callGas0.toB256 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 ::
          0 :: toWord :: ρ :: R) (balanceRequestMemory M sevm.currentTarget) callGas0)
      (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 ::
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
    (long0 : 32 ≤ d0.returnData.length)
    (code1 : ((afterSload sevm d0 7).getCode (d0.getStorVal sevm.currentTarget 7).toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
          Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
      Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
    (long1 : 32 ≤ d1.returnData.length)
    (gas0 : d0.gasLeft = callGas1 + 5 + sloadCost sevm d0 7 +
      temporalAccountAccessCost (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr + 219)
    (gas1 : d1.gasLeft = G + 70)
    (body : SFunc.RunExact cert.prog sevm
      (St d1 (Bytes.toB256 (d1.returnData.take 32) :: 0 ::
        Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget d1.returnData) G) MintBalanceSite.second.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: toWord :: ρ :: R) M
        (callGas0 + 5 + sloadCost sevm b 6 +
          temporalAccountAccessCost (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr + 166))
      t_1094_c41 o := by
  have request0 := balanceRequestMemory_ptr mem sevm.currentTarget
  have reply0 := balanceReplyMemory_ptr d0.returnData request0
  have request1 := balanceRequestMemory_ptr reply0 sevm.currentTarget
  have decoded1 := mintBalanceDecode_exact (lengthWord := d1.returnData.length.toB256) MintBalanceSite.second request1
    reply0.wf long1 (by simp only [List.length_cons]; omega) body
  have observed1 := mintBalanceObservation_exact (z := 0) MintBalanceSite.second fork request1
    (by simp only [List.length_cons]; omega) call1 success1
    (show d1.gasLeft = (G + 6) + 64 by omega) long1 decoded1
  have requested1 := mintSecondRequest_exact fork reply0 room code1 observed1
  have decoded0 := mintBalanceDecode_exact (lengthWord := d0.returnData.length.toB256) MintBalanceSite.first request0 mem.wf long0
    (by simp only [List.length_cons]; omega) requested1
  have observed0 := mintBalanceObservation_exact (z := 0) MintBalanceSite.first fork request0
    (by simp only [List.length_cons]; omega) call0 success0 (by omega) long0 decoded0
  exact mintFirstRequest_exact fork mem room code0 observed0

/-- Checked amounts, the real factory call, all fee arms and both pricing arms construct
one complete callee-local continuation from primitive guards and charges. -/
theorem mintFeePricing_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {feeResidual finalGas callGas sourceCost supplyCost loadCost creditCost : Nat}
    {b1 b0 r1 r0 toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (balanceBound0 : b0.toNat < 2 ^ 112) (balanceBound1 : b1.toNat < 2 ^ 112)
    (cover0 : r0 ≤ b0) (cover1 : r1 ≤ b1) (room : R.length ≤ 990)
    (code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0)
    (call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: 0x1233 ::
          mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: 0x1233 :: mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
    (width : 32 ≤ d.returnData.length)
    (returnedGas : d.gasLeft = feeResidual +
      feeBranchCharge sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 sourceCost supplyCost loadCost creditCost +
      sloadCost sevm d 11 + 120)
    (forward : FeeBranchForward sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual sourceCost supplyCost loadCost creditCost)
    (pricing : MintAfterFeeEnv sevm
      (feeBranchPost sevm (feeKLastWorld sevm d)
        (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual)
      (feeOnWord (Bytes.toB256 (d.returnData.take 32))) toWord (b0-r0) (b1-r1) b0 b1 r0 r1 finalGas)
    (residualCharge : feeResidual = pricing.armGas + sloadCost sevm
      (feeBranchPost sevm (feeKLastWorld sevm d)
        (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual) 0 + 28) :
    SFunc.RunExact cert.prog sevm
      (St b (b1 :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) M
        (callGas + sloadCost sevm b 5 +
          temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 360))
      MintBalanceSite.second.afterDecodeTree
      (.returned (pricing.post
        (feeBranchPost sevm (feeKLastWorld sevm d)
          (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
          (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
          (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual).memory R ρ)) := by
  let feePost := feeBranchPost sevm (feeKLastWorld sevm d)
    (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
    (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
    (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual
  have machine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm d)
    (R := mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
    (K := feeKLastWord sevm d) (w := Bytes.toB256 (d.returnData.take 32))
    (r0 := r0) (r1 := r1) (G := feeResidual)
    (feeReplyMemory_ptr d.returnData (feeRequestMemory_ptr mem))
  have priced := mintAfterFee_exact (R := R) (oldLiquidity := 0) (ρ := ρ) fork machine.2 bound0 bound1
    balanceBound0 balanceBound1 (by omega) pricing
  have self : feePost = St feePost
      (feeOnWord (Bytes.toB256 (d.returnData.take 32)) :: 0 :: (b1-r1) :: (b0-r0) ::
        b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R) feePost.memory feeResidual := by
    have gas : feePost.gasLeft = feeResidual :=
      (feeBranchPost_facts (st := { State.empty 0 0 with kLast := feeKLastWord sevm d })).2.1
    have eq := St.self (d := feePost) (by simpa only [feePost,mintFeeLocals] using machine.1) rfl
    rw [gas] at eq
    exact eq
  have suffix : SFunc.RunExact cert.prog sevm feePost t_1233_c41
      (.returned (pricing.post feePost.memory R ρ)) := by
    rw [self]
    simpa only [feePost,← residualCharge,St,Devm.memory_setMach] using priced
  have callee := fee68_exact fork mem bound0 bound1 (by simp only [mintFeeLocals,List.length_cons]; omega)
    code call success width returnedGas forward
  have composed := mintAmountsFee_exact bound0 bound1 cover0 cover1 (by omega) callee
    (SFunc.runExact_iff_runExactCut_nil.mp suffix)
  have raw := SFunc.runExact_iff_runExactCut_nil.mpr composed
  convert raw using 1

end Blanc.Lift.UniswapV2Pair
