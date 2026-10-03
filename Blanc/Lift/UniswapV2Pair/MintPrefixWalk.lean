import Blanc.Lift.UniswapV2Pair.MintSource
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesCore
import Blanc.Lift.UniswapV2Pair.BalanceCallWalk

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

/-- The real lock store preserves the finite representation while setting source unlocked to zero. -/
theorem WriterRep.mint_lock_store {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : WriterRep K (s.set 12 0) { st with unlocked := 0 } := by
  have unchanged (n : B256) (off : (12 : B256) ≠ n) :
      (s.set 12 0).get n = s.get n := Stor.get_set_ne s off 0
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches]
    rw [unchanged 0 (by decide),unchanged 3 (by decide),unchanged 5 (by decide),
      unchanged 6 (by decide),unchanged 7 (by decide),unchanged 8 (by decide),
      unchanged 9 (by decide),unchanged 10 (by decide),unchanged 11 (by decide),Stor.get_set_self]
    exact ⟨rep.fixed.1,rep.fixed.2.1,rep.fixed.2.2.1,rep.fixed.2.2.2.1,
      rep.fixed.2.2.2.2.1,rep.fixed.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.2.2.1,rfl⟩
  · intro k nonzero
    by_cases hit : k = 12
    · exact .inl (hit.symm ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    · rw [unchanged k (Ne.symm hit)] at nonzero
      exact rep.support k nonzero
  · intro k tracked
    have off : (12 : B256) ≠ k.slot :=
      fun h => rep.apart k tracked (h ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off]
    cases k <;> exact rep.selected _ tracked
  · intro k outside
    cases k <;> exact rep.logicalZero _ outside

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

/-- Complete actual1011 inverse to the finite mint suffix, with only actual touched-recipient obligations. -/
theorem mintSourcePrefix_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (frame : Frame) (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (toWord :: ρ :: R) M G) t_1011_c41 (.done o)) :
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
          (Bytes.toB256 (out1.take 32)) balance0 r1 r0 toWord ρ bound0 bound1 frame o := by
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
  exact getterWord_tail_inv mem (by simpa only [t_039b_c86, t_039b_c98] using run)

end Blanc.Lift.UniswapV2Pair
