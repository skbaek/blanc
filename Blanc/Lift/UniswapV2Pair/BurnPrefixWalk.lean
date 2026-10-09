import Blanc.Lift.UniswapV2Pair.BurnPricingWalk
import Blanc.Lift.UniswapV2Pair.FeeMintSource
import Blanc.Lift.UniswapV2Pair.WriterLockStorage
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesCore
import Blanc.Lift.UniswapV2Pair.BalanceCallWalk
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.InvWalkProvenance

/-! Literal Burn lock, reserve and initial balance-observation prefix. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Burn's literal lock test creates both output temporaries and reads the entry
lock before any write. The successful arm retains the original relation. -/
theorem burnLockGuard_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ ∃ gas,
      SFunc.RunCutP P cert.prog sevm C
        (St (afterSload sevm b 12) (0 :: 0 :: toWord :: extρ :: R) M gas) t_1469_c37 seg := by
  have h := run
  unfold t_13f5_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sload fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_eq (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, gas, tail⟩
  · exact (failed.false_of_noOk (by decide : t_1403_c37.noOk = true)).elim
  · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
    have unlocked : b.getStorVal sevm.currentTarget 12 = 1 := by
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact (accepted rfl).elim
    exact ⟨unlocked, gas, tail⟩

def burnLockedWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 12) 12 0

/-- Burn's actual lock write and getter56 call cache all three reserve fields
before the two initial balance queries. No cached-reserve premise is added. -/
theorem burnReservePrefix_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧ ∃ gas,
      let locked := burnLockedWorld sevm b
      SFunc.RunCutP P cert.prog sevm C (St (afterSload sevm locked 8)
        (reserveTimestampRead (locked.getStorVal sevm.currentTarget 8) ::
         reserve1Read (locked.getStorVal sevm.currentTarget 8) ::
         reserve0Read (locked.getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M gas) t_1479_c37 seg := by
  obtain ⟨unlocked, _, h⟩ := burnLockGuard_inv project fork run
  unfold t_1469_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  have mutable := ri_sstore_nonstatic fork (project hd)
  obtain ⟨_, rfl⟩ := ri_sstore fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
  | callRet d lookup pop callee tail =>
    change some t_0d90_c56 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨gas, returned⟩ := reserves_callee_inv fork (callee.mono project)
    cases returned
    exact ⟨unlocked, mutable, gas, tail⟩
  | callHalt d lookup pop callee =>
    change some t_0d90_c56 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, returned⟩ := reserves_callee_inv fork (callee.mono project)
    cases returned

/-- Both token slots are cached before Burn's initial external observations. -/
def burnTokensWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm b 6) 7

/-- Literal Burn staging obtains the first token target from storage, preserves
both cached token words, and passes the actual code guard into STATICCALL. -/
theorem burnInitialFirstRequest_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {timestamp r1 r0 toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (timestamp :: r1 :: r0 :: 0 :: 0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_1479_c37 seg) :
    let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
    let t0 := mask &&& b.getStorVal sevm.currentTarget 6
    let t1 := mask &&& (afterSload sevm b 6).getStorVal sevm.currentTarget 7
    let loaded := burnTokensWorld sevm b
    (loaded.getCode t0.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP P cert.prog sevm C
        (St (temporalAccountAccessBase loaded t0.toAdr)
          (0 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t0 ::
            0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
          (balanceRequestMemory M sevm.currentTarget) gas) t_14fb_c37 seg := by
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 := mem2.read_self (by decide : 64 + 32 ≤ 192)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  have h := run
  unfold t_1479_c37 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sload fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sload fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, mem.read_self (by decide)] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  have address := of_run_address (project hd)
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have eq := St.of_stackRel address
  rw [stack] at eq
  rw [eq] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_extcodesize fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, gas, tail⟩
  · exact (failed.false_of_noOk (by decide : t_14f7_c37.noOk = true)).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have nonzero : ((burnTokensWorld sevm b).getCode
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0 := by
      intro eq
      change B256.eqCheck (((burnTokensWorld sevm b).getCode
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal sevm.currentTarget 6).toAdr).size.toB256) 0 = 0 at zero
      rw [eq, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero] at tail
    refine ⟨nonzero, gas, ?_⟩
    simpa only [burnTokensWorld, balanceRequestMemory, balanceOfSelectorWord,
      show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
        (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
      show Bytes.toB256 [6] = (6 : B256) from rfl,
      show Bytes.toB256 [7] = (7 : B256) from rfl,
      show Bytes.toB256 [0] = (0 : B256) from rfl,
      show Bytes.toB256 [32] = (32 : B256) from rfl,
      show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
      show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
      show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using tail

inductive BurnInitialBalanceSite where
  | first
  | second

def BurnInitialBalanceSite.callTree : BurnInitialBalanceSite → SFunc
  | .first => t_14fb_c37
  | .second => t_1599_c37

def BurnInitialBalanceSite.returnTree : BurnInitialBalanceSite → SFunc
  | .first => t_150f_c37
  | .second => t_15ad_c37

def BurnInitialBalanceSite.decodeTree : BurnInitialBalanceSite → SFunc
  | .first => t_1525_c37
  | .second => t_15c3_c37

def BurnInitialBalanceSite.afterDecodeTree (site : BurnInitialBalanceSite) : SFunc :=
  match site.decodeTree with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

/-- The first actual answer replaces its balance temporary; the second request
uses the already cached token1 word and preserves token0 and the old reserves. -/
theorem burnInitialSecondRequest_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {b0 token1 token0 r1 r0 toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (b0 :: 0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      BurnInitialBalanceSite.first.afterDecodeTree seg) :
    let t1 := token1 &&& 0xffffffffffffffffffffffffffffffffffffffff
    (b.getCode t1.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP P cert.prog sevm C
        (St (temporalAccountAccessBase b t1.toAdr)
          (0 :: t1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t1 ::
            0 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
          (balanceRequestMemory M sevm.currentTarget) gas) t_1599_c37 seg := by
  have mem2 := balanceRequestMemory_ptr mem sevm.currentTarget
  change PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) at mem2
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 := mem2.word
  have same2 := mem2.read_self (by decide : 64 + 32 ≤ 192)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  have h := run
  unfold BurnInitialBalanceSite.afterDecodeTree BurnInitialBalanceSite.decodeTree t_1525_c37 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, mem.read_self (by decide)] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  have address := of_run_address (project hd)
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have eq := St.of_stackRel address
  rw [stack] at eq
  rw [eq] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, eq⟩ := ri_mload (project hd)
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read2, same2] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_extcodesize fork (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨accepted, gas, tail⟩
  · exact (failed.false_of_noOk (by decide : t_1595_c37.noOk = true)).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have nonzero : (b.getCode
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 := by
      intro eq
      change B256.eqCheck ((b.getCode
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256) 0 = 0 at zero
      rw [eq, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero] at tail
    refine ⟨nonzero, gas, ?_⟩
    simpa only [balanceRequestMemory, balanceOfSelectorWord,
      show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
        (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl,
      show Bytes.toB256 [0] = (0 : B256) from rfl,
      show Bytes.toB256 [32] = (32 : B256) from rfl,
      show Bytes.toB256 [112, 160, 130, 49] = (0x70a08231 : B256) from rfl,
      show (128 : B256) - 128 + Bytes.toB256 [36] = 36 from by decide,
      show (128 : B256) + Bytes.toB256 [36] = 164 from by decide] using tail

/-- The real lock store transports the entry representation into Burn's locked world. -/
theorem WriterRep.burn_locked_world {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((burnLockedWorld sevm b).getStor sevm.currentTarget) { st with unlocked := 0 } := by
  rw [burnLockedWorld, afterSstore_getStor_self, afterSload_getStor]
  exact rep.mint_lock_store

end Blanc.Lift.UniswapV2Pair
