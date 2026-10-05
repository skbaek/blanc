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

/-- Each actual initial Burn observation retains its original STATICCALL,
complete reply, successful flag and decoded word, using shared call/width/memory
producers. Neither query acceptance nor its answer is an endpoint premise. -/
theorem burnInitialBalanceRead_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {z token a x y : B256} {seg : Seg} (site : BurnInitialBalanceSite)
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) G) site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (balanceRequestMemory M sevm.currentTarget)
        128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm b token.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      PtrMem 128 192 (balanceReplyMemory M sevm.currentTarget out) ∧
      (∃ decodeGas, SFunc.RunCutP P cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: R)
          (balanceReplyMemory M sevm.currentTarget out) decodeGas) site.decodeTree seg) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (Bytes.toB256 (out.take 32) :: R)
          (balanceReplyMemory M sevm.currentTarget out) tailGas) site.afterDecodeTree seg := by
  have observed : ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas) (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) (balanceRequestMemory M sevm.currentTarget)
        128 36 128 32 1 out ∧
      out.length < 2 ^ 256 ∧
      StaticAnswered sevm b token.toAdr
        ((balanceRequestMemory M sevm.currentTarget).read 128 36).1 out ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (0 :: a :: x :: y :: R) (balanceReplyMemory M sevm.currentTarget out) tailGas)
        site.returnTree seg := by
    cases site
    · exact staticCallGuard_invP [0x15, 0x0f] (by decide) rfl project fork (by decide) run
    · exact staticCallGuard_invP [0x15, 0xad] (by decide) rfl project fork (by decide) run
  obtain ⟨gw, callGas, d, out, _, call, post, width, answered, tail⟩ := observed
  have replyMem := balanceReplyMemory_ptr out mem
  have full : d.returnData.length < 2 ^ 256 := by rw [post.returnData]; exact width
  have guarded : 32 ≤ d.returnData.length ∧ ∃ gas,
      SFunc.RunCutP P cert.prog sevm C
        (St d (d.returnData.length.toB256 :: 128 :: R)
          (balanceReplyMemory M sevm.currentTarget out) gas) site.decodeTree seg := by
    cases site
    · exact returnWidthGuard_invP [0x15, 0x25] (by decide) rfl project replyMem full (by decide) tail
    · exact returnWidthGuard_invP [0x15, 0xc3] (by decide) rfl project replyMem full (by decide) tail
  obtain ⟨long, _, decoded⟩ := guarded
  rw [post.returnData] at long decoded
  have originalDecoded := decoded
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape] at decoded
  obtain ⟨_, decoded⟩ := ric_destP decoded
  obtain ⟨_, step, decoded⟩ := ric_nextP decoded; obtain ⟨_, rfl⟩ := ri_pop (project step)
  obtain ⟨loaded, step, decoded⟩ := ric_nextP decoded
  obtain ⟨tailGas, eq⟩ := ri_mload (project step)
  rw [show (128 : B256).toNat = 128 from rfl,
    balanceReplyMemory_word wf sevm.currentTarget out long, replyMem.read_self (by decide)] at eq
  subst loaded
  rw [balanceRequestMemory_read wf] at answered
  exact ⟨gw, callGas, d, out, tailGas, call, post, long, width, answered, replyMem, ⟨_, originalDecoded⟩, decoded⟩

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

/-- Both initial Burn answers come from one literal invocation after the entry
lock and reserve cache. STATICCALL preserves all storage, logs and parent output;
its captured answers and exact memory feed the later liquidity/fee/pricing path. -/
theorem burnInitialBalances_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (gas : Nat),
      let locked := burnLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
      let t0 := mask &&& reserveWorld.getStorVal sevm.currentTarget 6
      let t1 := mask &&& (afterSload sevm reserveWorld 6).getStorVal sevm.currentTarget 7
      let loaded := burnTokensWorld sevm reserveWorld
      let target1 := t1 &&& mask
      let w0 := temporalAccountAccessBase loaded t0.toAdr
      let w1 := temporalAccountAccessBase d0 target1.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let M1 := balanceReplyMemory M0 sevm.currentTarget out1
      (loaded.getCode t0.toAdr).size.toB256 ≠ 0 ∧
      P sevm (St w0 (gw0 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        t0 :: 0 :: t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: t0 :: 0 :: t1 :: t0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R) (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      StaticAnswered sevm w0 t0.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      (d0.getCode target1.toAdr).size.toB256 ≠ 0 ∧
      P sevm (St w1 (gw1 :: target1 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        target1 :: 0 :: Bytes.toB256 (out0.take 32) :: t1 :: t0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R) (balanceRequestMemory M0 sevm.currentTarget) callGas1)
        (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1 (164 :: 0x70a08231 :: target1 :: 0 :: Bytes.toB256 (out0.take 32) ::
        t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      StaticAnswered sevm w1 target1.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor locked a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧ PtrMem 128 192 M1 ∧
      (∃ decodeGas, SFunc.RunCutP P cert.prog sevm C
        (St d1 (out1.length.toB256 :: 128 :: 0 :: Bytes.toB256 (out0.take 32) ::
          t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M1 decodeGas) t_15c3_c37 seg) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: 0 :: Bytes.toB256 (out0.take 32) :: t1 :: t0 ::
          r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M1 gas)
        BurnInitialBalanceSite.second.afterDecodeTree seg := by
  obtain ⟨unlocked, mutable, _, reserves⟩ := burnReservePrefix_inv project fork run
  obtain ⟨code0, _, first⟩ := burnInitialFirstRequest_inv project fork mem reserves
  have request0 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  obtain ⟨gw0, callGas0, d0, out0, _, call0, post0, long0, width0, answered0, reply0, decode0, tail0⟩ :=
    burnInitialBalanceRead_inv .first project fork request0 mem.wf first
  obtain ⟨code1, _, second⟩ := burnInitialSecondRequest_inv project fork reply0 tail0
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget) :=
    balanceRequestMemory_ptr reply0 sevm.currentTarget
  obtain ⟨gw1, callGas1, d1, out1, gas, call1, post1, long1, width1, answered1, reply1, decode1, tail1⟩ :=
    burnInitialBalanceRead_inv .second project fork request1 reply0.wf second
  have stor0 : ∀ a, Devm.getStor d0 a = Devm.getStor (burnLockedWorld sevm b) a := by
    intro a
    refine (post0.stor a).trans ?_
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    change Devm.getStor (burnTokensWorld sevm (afterSload sevm (burnLockedWorld sevm b) 8)) a = _
    rw [burnTokensWorld, afterSload_getStor, afterSload_getStor, afterSload_getStor]
    simp only [Devm.getStor, Devm.getAcct]
  have stor1 : ∀ a, Devm.getStor d1 a = Devm.getStor (burnLockedWorld sevm b) a := by
    intro a
    refine (post1.stor a).trans ?_
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    exact stor0 a
  have logs0 : d0.logs = b.logs := by
    refine post0.logs.trans ?_
    rw [temporalAccountAccessBase_logs, burnTokensWorld,
      afterSload_logs, afterSload_logs, afterSload_logs, burnLockedWorld,
      afterSstore_logs, afterSload_logs]
  have logs1 : d1.logs = b.logs := post1.logs.trans ((temporalAccountAccessBase_logs _ _).trans logs0)
  have output0 : d0.output = b.output := by
    refine (post0.output rfl).trans ?_
    rw [temporalAccountAccessBase_output, burnTokensWorld,
      afterSload_output, afterSload_output, afterSload_output, burnLockedWorld,
      afterSstore_output, afterSload_output]
  have output1 : d1.output = b.output :=
    (post1.output rfl).trans ((temporalAccountAccessBase_output _ _).trans output0)
  exact ⟨unlocked, mutable, gw0, callGas0, d0, out0, gw1, callGas1, d1, out1, gas,
    code0, call0, post0, long0, width0, answered0, code1, call1, post1,
    long1, width1, answered1, stor0, stor1, logs1, output1, reply1, decode1, tail1⟩

/-- The real lock store transports the entry representation into Burn's locked world. -/
theorem WriterRep.burn_locked_world {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((burnLockedWorld sevm b).getStor sevm.currentTarget) { st with unlocked := 0 } := by
  rw [burnLockedWorld, afterSstore_getStor_self, afterSload_getStor]
  exact rep.mint_lock_store

/-- The actual initial calls provide represented locked storage and the literal
liquidity-sampling continuation. No representation of a chosen endpoint is assumed. -/
theorem burnInitialBalances_writer_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (d0 : Devm) (out0 : Bytes) (d1 : Devm) (out1 : Bytes) (gas : Nat),
      let locked := burnLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
      let t0 := mask &&& reserveWorld.getStorVal sevm.currentTarget 6
      let t1 := mask &&& (afterSload sevm reserveWorld 6).getStorVal sevm.currentTarget 7
      let w0 := temporalAccountAccessBase (burnTokensWorld sevm reserveWorld) t0.toAdr
      let w1 := temporalAccountAccessBase d0 (t1 &&& mask).toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let M1 := balanceReplyMemory M0 sevm.currentTarget out1
      (∃ call0, StepIn D sevm call0 (.exec .staticcall) d0) ∧
      (∃ call1, StepIn D sevm call1 (.exec .staticcall) d1) ∧
      StaticAnswered sevm w0 t0.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      StaticAnswered sevm w1 (t1 &&& mask).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor locked a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧ PtrMem 128 192 M1 ∧
      r0.toNat < 2 ^ 112 ∧ r1.toNat < 2 ^ 112 ∧
      feeBurnBalance1 M1 = Bytes.toB256 (out1.take 32) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d1 (out1.length.toB256 :: 128 :: 0 :: Bytes.toB256 (out0.take 32) ::
          t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M1 gas) t_15c3_c37 seg := by
  obtain ⟨unlocked, mutable, gw0, cg0, d0, out0, gw1, cg1, d1, out1, _,
    code0, call0, post0, long0, width0, answered0, code1, call1, post1, long1,
    width1, answered1, stor0, stor1, logs1, output1, reply1, ⟨gas, decoded⟩, tail⟩ :=
    burnInitialBalances_inv (fun h => StepIn.toRun h) fork mem run
  have lockedRep : WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } := by
    rw [stor1]
    exact rep.burn_locked_world
  have bound0 : (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve0Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have bound1 : (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      < 2 ^ 112 := by
    unfold reserve1Read
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat _ (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have cached : feeBurnBalance1
      (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1) =
      Bytes.toB256 (out1.take 32) := by
    exact balanceReplyMemory_word (balanceReplyMemory_ptr out0
      (balanceRequestMemory_ptr mem sevm.currentTarget)).wf sevm.currentTarget out1 long1
  exact ⟨unlocked, mutable, d0, out0, d1, out1, gas, ⟨_, call0⟩, ⟨_, call1⟩,
    answered0, answered1, long0, width0, long1, width1, lockedRep, stor1,
    logs1, output1, reply1, bound0, bound1, cached, decoded⟩

/-- Actual Burn entry reaches the existing fee source caller. Freshness is
requested only for a same-D continuation that this prefix actually produces. -/
theorem burnEntry_fee_source_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {toWord extρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (fresh :
      let locked := burnLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
      let t0 := mask &&& reserveWorld.getStorVal sevm.currentTarget 6
      let t1 := mask &&& (afterSload sevm reserveWorld 6).getStorVal sevm.currentTarget 7
      ∀ (out0 : Bytes) (d1 : Devm) (out1 : Bytes) (gas : Nat),
        let M1 := balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1
        WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } →
        SFunc.RunCutP (StepIn D) cert.prog sevm C
          (St d1 (out1.length.toB256 :: 128 :: 0 :: Bytes.toB256 (out0.take 32) ::
            t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M1 gas) t_15c3_c37 seg →
        FeeMintSourceFresh K { st with unlocked := 0 } D sevm (feeBurnWorld sevm d1)
          (burnFeeLocals (feeBurnLiquidity sevm d1) (feeBurnBalance1 M1)
            (Bytes.toB256 (out0.take 32)) t1 t0 r1 r0 toWord extρ R)
          (feeBurnMemory M1 sevm.currentTarget) r1 r0 0x15e2)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (toWord :: extρ :: R) M G) t_13f5_c37 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (d0 : Devm) (out0 : Bytes) (d1 : Devm) (out1 : Bytes) (feeGas : Nat) (feePost : Devm),
      let locked := burnLockedWorld sevm b
      let reserveWorld := afterSload sevm locked 8
      let r0 := reserve0Read (locked.getStorVal sevm.currentTarget 8)
      let r1 := reserve1Read (locked.getStorVal sevm.currentTarget 8)
      let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
      let t0 := mask &&& reserveWorld.getStorVal sevm.currentTarget 6
      let t1 := mask &&& (afterSload sevm reserveWorld 6).getStorVal sevm.currentTarget 7
      let w0 := temporalAccountAccessBase (burnTokensWorld sevm reserveWorld) t0.toAdr
      let w1 := temporalAccountAccessBase d0 (t1 &&& mask).toAdr
      let M1 := balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1
      let locals := burnFeeLocals (feeBurnLiquidity sevm d1) (feeBurnBalance1 M1)
        (Bytes.toB256 (out0.take 32)) t1 t0 r1 r0 toWord extρ R
      (∃ call0, StepIn D sevm call0 (.exec .staticcall) d0) ∧
      (∃ call1, StepIn D sevm call1 (.exec .staticcall) d1) ∧
      StaticAnswered sevm w0 t0.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      StaticAnswered sevm w1 (t1 &&& mask).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      WriterRep K (d1.getStor sevm.currentTarget) { st with unlocked := 0 } ∧
      feeBurnLiquidity sevm d1 = st.balanceOf sevm.currentTarget ∧
      feeBurnBalance1 M1 = Bytes.toB256 (out1.take 32) ∧
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (feeBurnWorld sevm d1) (r1 :: r0 :: 0x15e2 :: locals)
          (feeBurnMemory M1 sevm.currentTarget) feeGas) t_26ec_c68 (.returned feePost) ∧
      Nonempty (FeeMintSourceObservation K { st with unlocked := 0 } D sevm (feeBurnWorld sevm d1)
        locals (feeBurnMemory M1 sevm.currentTarget) r1 r0 0x15e2 (.returned feePost)) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 seg := by
  obtain ⟨unlocked, mutable, d0, out0, d1, out1, gas, call0, call1, answered0, answered1,
    long0, width0, long1, width1, feeRep, stor1, logs1, output1, reply1,
    bound0, bound1, balance1, decoded⟩ := burnInitialBalances_writer_inv fork mem rep run
  obtain ⟨cached, feeGas, feePost, callee, source, continuation⟩ :=
    feeBurn_source_caller_inv fork reply1 feeRep tracked bound0 bound1
      (fresh out0 d1 out1 gas feeRep decoded) decoded
  exact ⟨unlocked, mutable, d0, out0, d1, out1, feeGas, feePost, call0, call1,
    answered0, answered1, long0, width0, long1, width1, feeRep, cached,
    balance1, callee, source, continuation⟩

end Blanc.Lift.UniswapV2Pair
