import Blanc.Lift.UniswapV2Pair.Consumption
import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.BalanceCallWalk
import Blanc.Lift.UniswapV2Pair.GetterWalk
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.InvWalkDispatch

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual post-update continuation performs the lock-slot write and
returns the caller tail, retaining the selected store metadata. -/
theorem syncUnlock_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (tag :: R) M G) t_1fd4_c31 o) :
    sevm.isStatic = false ∧ ∃ gas,
      o = .returned (St (afterSstore sevm b 12 1) R M gas) := by
  have h := run.cut
  unfold t_1fd4_c31 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have mutable := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨gas, result⟩ := ric_ret h
  exact ⟨mutable, gas, Seg.done.inj result⟩

/-- The same literal unlock suffix has seven local gas before its selected
store and eight gas for the return jump. -/
theorem syncUnlock_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (room : R.length ≤ 1021)
    (sentry : gCallStipend < G + 8 + sstoreCost sevm b 12 1) :
    SFunc.RunExact cert.prog sevm
      (St b (tag :: R) M (G + 8 + sstoreCost sevm b 12 1 + 7)) t_1fd4_c31
      (.returned (St (afterSstore sevm b 12 1) R M G)) := by
  unfold t_1fd4_c31
  apply rx_dest
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  apply rx_sstore fork sentry static
  exact rx_ret

/-- The slot-8 extraction is reached after the second answer was decoded.
The cached update operands are exactly this current selected word. -/
theorem syncReserveLoad_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (balance1 :: balance0 :: 0x1fd4 :: tag :: R) M G)
      SyncBalanceSite.second.afterDecodeTree o) :
    ∃ gas, SFunc.Run cert.prog sevm
      (St (afterSload sevm b 8)
        (0x22e0 :: reserve1Read (b.getStorVal sevm.currentTarget 8) ::
          reserve0Read (b.getStorVal sevm.currentTarget 8) ::
          balance1 :: balance0 :: 0x1fd4 :: tag :: R) M gas)
      (.callNext 60 t_1fd4_c31) o := by
  have h := run.cut
  change SFunc.RunCut _ _ [] _ (.next (.push [8] _) _) _ at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨gas, rfl⟩ := ri_push hd
  exact ⟨gas, h.uncut⟩

/-- The actual post-decoder reserve extraction and internal call use 43 local
gas besides the selected slot-8 read and the supplied shared-update run. -/
theorem syncReserveLoad_exact {sevm : Sevm} {b D : Devm} {R : List B256} {M : Mem}
    {G load : Nat} {balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1016)
    (charge : load = sloadCost sevm b 8)
    (callee : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (reserve1Read (b.getStorVal sevm.currentTarget 8) ::
          reserve0Read (b.getStorVal sevm.currentTarget 8) ::
          balance1 :: balance0 :: 0x1fd4 :: tag :: R) M G) t_22e0_c60 (.returned D))
    (body : SFunc.RunExact cert.prog sevm D t_1fd4_c31 o) :
    SFunc.RunExact cert.prog sevm
      (St b (balance1 :: balance0 :: 0x1fd4 :: tag :: R) M (G + load + 43))
      SyncBalanceSite.second.afterDecodeTree o := by
  change SFunc.RunExact _ _ _ (.next (.push [8] _) _) _
  apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 40 = (G + 40) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b.getStorVal sevm.currentTarget 8) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := reserve0Read (b.getStorVal sevm.currentTarget 8)) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := reserve1Read (b.getStorVal sevm.currentTarget 8)) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x22e0) rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet rfl callee body

/-- The actual caller loads the cached reserves once, immediately before the
shared update. These images retain that load's access metadata. -/
def syncUpdatedWorld (sevm : Sevm) (b : Devm) (balance0 balance1 : B256) : Devm :=
  updateWorld sevm (afterSload sevm b 8)
    (reserve0Read (b.getStorVal sevm.currentTarget 8))
    (reserve1Read (b.getStorVal sevm.currentTarget 8)) balance0 balance1

def syncResultWorld (sevm : Sevm) (b : Devm) (balance0 balance1 : B256) : Devm :=
  afterSstore sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1

def syncResultMemory (sevm : Sevm) (b : Devm) (M : Mem)
    (balance0 balance1 : B256) : Mem :=
  updateMemory sevm (afterSload sevm b 8) M
    (reserve0Read (b.getStorVal sevm.currentTarget 8))
    (reserve1Read (b.getStorVal sevm.currentTarget 8)) balance0 balance1

/-- Successful bytes after the second decoder perform the actual shared update
and unlock, deriving both balance guards and preserving the exact caller tail. -/
theorem syncUpdateUnlock_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 n M)
    (run : SFunc.Run cert.prog sevm
      (St b (balance1 :: balance0 :: 0x1fd4 :: tag :: R) M G)
      SyncBalanceSite.second.afterDecodeTree o) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
      ∃ gas, o = .returned (St (syncResultWorld sevm b balance0 balance1) R
        (syncResultMemory sevm b M balance0 balance1) gas) := by
  obtain ⟨_, loadRun⟩ := syncReserveLoad_inv fork run
  obtain ⟨_, returning | halted⟩ := ric_call (g := t_22e0_c60) rfl loadRun.cut
  · obtain ⟨d, callee, continuation⟩ := returning
    obtain ⟨bound0, bound1, static, gas, result⟩ := update_inv fork mem callee
    have state := Outcome.returned.inj result
    subst d
    obtain ⟨_, finalGas, final⟩ := syncUnlock_inv fork continuation.uncut
    exact ⟨bound0, bound1, static, finalGas, final⟩
  · obtain ⟨d, callee, _⟩ := halted
    obtain ⟨_, _, _, _, impossible⟩ := update_inv fork mem callee
    cases impossible

/-- Compose the supplied actual shared-update run with the literal caller
load and unlock. The primitive store sentry remains a separate obligation. -/
theorem syncUpdateUnlock_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G updateGas load : Nat} {balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (room : R.length ≤ 1016) (charge : load = sloadCost sevm b 8)
    (sentry : gCallStipend < G + 8 +
      sstoreCost sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1)
    (callee : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (reserve1Read (b.getStorVal sevm.currentTarget 8) ::
          reserve0Read (b.getStorVal sevm.currentTarget 8) ::
          balance1 :: balance0 :: 0x1fd4 :: tag :: R) M updateGas) t_22e0_c60
      (.returned (St (syncUpdatedWorld sevm b balance0 balance1) (tag :: R)
        (syncResultMemory sevm b M balance0 balance1)
        (G + 8 + sstoreCost sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1 + 7)))) :
    SFunc.RunExact cert.prog sevm
      (St b (balance1 :: balance0 :: 0x1fd4 :: tag :: R) M (updateGas + load + 43))
      SyncBalanceSite.second.afterDecodeTree
      (.returned (St (syncResultWorld sevm b balance0 balance1) R
        (syncResultMemory sevm b M balance0 balance1) G)) := by
  refine syncReserveLoad_exact fork room charge callee ?_
  exact syncUnlock_exact fork static (by omega) sentry

/-- The caller's actual packed extraction agrees with the cached source
reserves when the selected current word has been transported across the calls. -/
theorem syncCachedReserves_source {st : State} {sevm : Sevm} {b : Devm}
    (slots : ReserveSlotMatches st sevm b) :
    (reserve0Read (b.getStorVal sevm.currentTarget 8)).toNat = st.reserve0.val ∧
    (reserve1Read (b.getStorVal sevm.currentTarget 8)).toNat = st.reserve1.val := by
  rw [slots.1, slots.2.1,
    B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256)),
    B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  exact ⟨rfl, rfl⟩

/-- Unlock changes only slot12 after the shared update; the other selected
slots still contain its exact packed and cumulative result. -/
theorem syncResultWorld_selected {sevm : Sevm} {b : Devm} {balance0 balance1 key : B256}
    (other : key ≠ 12) :
    (syncResultWorld sevm b balance0 balance1).getStorVal sevm.currentTarget key =
      (syncUpdatedWorld sevm b balance0 balance1).getStorVal sevm.currentTarget key := by
  unfold syncResultWorld
  change (Devm.getStor _ _).get key = _
  rw [afterSstore_getStor_self, Stor.get_set_ne _ (Ne.symm other)]
  rfl

/-- With the selected entry fields transported to the point after both calls,
the concrete update-and-unlock world carries the source update and Sync event. -/
theorem syncUpdateSource_result {st : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {balance0 balance1 : B256}
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    ∃ post event oracle,
      st.update ctx balance0 balance1 st.reserve0.val st.reserve1.val = .ok (post, event, oracle) ∧
      ReserveSlotMatches { post with unlocked := 1 } sevm (syncResultWorld sevm b balance0 balance1) ∧
      (syncResultWorld sevm b balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      (syncResultWorld sevm b balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      (syncResultWorld sevm b balance0 balance1).getStorVal sevm.currentTarget 12 = 1 ∧
      event = .sync balance0.toNat balance1.toNat ∧
      (syncResultWorld sevm b balance0 balance1).logs =
        b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  obtain ⟨cached0, cached1⟩ := syncCachedReserves_source slots
  have loadedSlots : ReserveSlotMatches st sevm (afterSload sevm b 8) := by
    simpa only [ReserveSlotMatches, getStorVal_afterSload] using slots
  obtain ⟨post, event, oracle, source, reserves, price0, price1, sync, logs⟩ :=
    update_source_result loadedSlots (by rw [getStorVal_afterSload]; exact cum0)
      (by rw [getStorVal_afterSload]; exact cum1) time pair
      (by rw [cached0]; exact st.reserve0.isLt) (by rw [cached1]; exact st.reserve1.isLt)
      bound0 bound1
  rw [cached0, cached1] at source
  refine ⟨post, event, oracle, source, ?_, ?_, ?_, ?_, sync, ?_⟩
  · simpa only [ReserveSlotMatches, syncResultWorld_selected (by decide : (8 : B256) ≠ 12),
      syncUpdatedWorld] using reserves
  · rw [syncResultWorld_selected (by decide : (9 : B256) ≠ 12)]
    exact price0
  · rw [syncResultWorld_selected (by decide : (10 : B256) ≠ 12)]
    exact price1
  · unfold syncResultWorld
    change (Devm.getStor _ _).get 12 = _
    rw [afterSstore_getStor_self, Stor.get_set_self]
  · rw [syncResultWorld, afterSstore_logs]
    simpa only [syncUpdatedWorld, afterSload_logs] using logs

/-- The literal code-size suffix after the forty-one preceding steps of each
balance request. The fallback is unused by both certificate projections. -/
def SyncBalanceSite.codeGuardTree (site : SyncBalanceSite) : SFunc :=
  match (match site with | .first => t_1e66_c31 | .second => t_1f07_c31) with
  | .dest (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (body)))))))))))))))))))))))))))))))))))))))))) => body
  | _ => .undefined

def SyncBalanceSite.codeFailureTree : SyncBalanceSite → SFunc
  | .first => t_1ed9_c31
  | .second => t_1f76_c31

def SyncBalanceSite.codeDestination : SyncBalanceSite → Bytes
  | .first => [0x1e, 0xdd]
  | .second => [0x1f, 0x7a]

private theorem syncCodeGuard_shape (site : SyncBalanceSite) :
    site.codeGuardTree = .next (.reg .extcodesize) (.next (.reg .iszero)
      (.next (.reg (.dup 0)) (.next (.reg .iszero)
        (.next (.push site.codeDestination (by cases site <;> decide))
          (.branch site.codeFailureTree site.callTree))))) := by
  cases site <;> rfl

/-- Successful passage through either actual code guard derives a nonzero
code-size word and preserves the same derivation predicate into the call. -/
theorem syncCodeGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {S : List B256} {C : List Nat} {M : Mem} {G : Nat} {token : B256} {seg : Seg}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (token :: S) M G) site.codeGuardTree seg) :
    (b.getCode token.toAdr).size.toB256 ≠ 0 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (temporalAccountAccessBase b token.toAdr) (0 :: S) M gas)
        site.callTree seg := by
  rw [syncCodeGuard_shape] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_extcodesize fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, tailRun⟩
  · have noFail : site.codeFailureTree.noOk = true := by cases site <;> decide
    exact False.elim (failed.false_of_noOk noFail)
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have nonzero : (b.getCode token.toAdr).size.toB256 ≠ 0 := by
      intro hz
      rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    refine ⟨nonzero, gas, ?_⟩
    simpa only [zero] using tailRun

/-- The literal guard charges its selected account access and twenty-two
local gas before entering the actual balance call destination. -/
theorem syncCodeGuard_exact {sevm : Sevm} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {token : B256} {o : Outcome}
    (site : SyncBalanceSite) (fork : CoveredFork sevm.benvStat.fork)
    (room : S.length ≤ 1021) (nonzero : (b.getCode token.toAdr).size.toB256 ≠ 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (temporalAccountAccessBase b token.toAdr) (0 :: S) M G) site.callTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (token :: S) M (G + 22 + temporalAccountAccessCost b token.toAdr))
      site.codeGuardTree o := by
  rw [syncCodeGuard_shape]
  apply rx_extcodesize fork (by omega)
  have zero : B256.eqCheck (b.getCode token.toAdr).size.toB256 0 = 0 := by
    simp only [B256.eqCheck, nonzero, ite_false]
  apply rx_iszero zero (by omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  cases site
  · apply rx_push (w := 0x1edd) rfl (by simp only [List.length_cons]; omega)
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body
  · apply rx_push (w := 0x1f7a) rfl (by simp only [List.length_cons]; omega)
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body


/-- The actual first decoder is followed by the slot-7 load and the second
balanceOf request. The token is read from the first call's resulting world. -/
theorem syncSecondRequest_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {balance0 tag : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (balance0 :: 0x1fd4 :: tag :: R) M G)
      SyncBalanceSite.first.afterDecodeTree seg) :
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St (afterSload sevm b 7)
        ((b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) gas)
      SyncBalanceSite.second.codeGuardTree seg := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 :=
    mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  change SFunc.RunCutP _ _ _ _ _ (.next (.push [7] _) _) _ at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read0, same0] at hd; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  have hp := of_run_address (StepIn.toRun hs)
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have hd := St.of_stackRel hp
  rw [stack] at hd
  rw [hd] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read2, same2] at hd; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [ff20_eq, and_mask_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨gas, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  exact ⟨gas, run⟩


/-- Thirty-eight fixed-charge instructions cost113 gas, in addition to the
selected slot-7 read. Both stores fit the192-byte scratch allocation. -/
theorem syncSecondRequest_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load : Nat} {balance0 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (room : R.length ≤ 1010) (charge : load = sloadCost sevm b 7)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 7)
        ((b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
         (b.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
         balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) G)
      SyncBalanceSite.second.codeGuardTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (balance0 :: 0x1fd4 :: tag :: R) M (G + load + 113))
      SyncBalanceSite.first.afterDecodeTree o := by
  have mem1 : PtrMem 128 192 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  change SFunc.RunExact _ _ _ (.next (.push [7] _) _) _
  apply rx_push (w := 7) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 110 = (G + 110) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word
    (mem.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + 90) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St (afterSload sevm b 7)
      (sevm.currentTarget.toB256 :: 128 :: 64 :: b.getStorVal sevm.currentTarget 7 ::
       balance0 :: 0x1fd4 :: tag :: R) (M.write 128 balanceOfSelectorWord.toBytes) (G + 90)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 3)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word
    (mem2.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap3
  apply rx_and (and_mask_word _) (by simp only [List.length_cons]; omega)
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
  exact body


/-- The two observations come from the actual first call, its decoded world,
the intervening slot-7/request walk, and the actual second call in that order. -/
theorem syncBalancePair_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat}
    {token0 tag : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (token0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) G)
      SyncBalanceSite.first.codeGuardTree seg) :
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 : Nat),
      let w0 := temporalAccountAccessBase b token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (b.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d0 (balance0 :: 0x1fd4 :: tag :: R) M0 decodedGas0)
        SyncBalanceSite.first.afterDecodeTree seg ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1 (164 :: 0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor b a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor b a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: balance0 :: 0x1fd4 :: tag :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        SyncBalanceSite.second.afterDecodeTree seg := by
  obtain ⟨code0, guardGas0, firstCall⟩ := syncCodeGuard_inv .first fork run
  obtain ⟨gw0, callGas0, d0, out0, decodedGas0, call0, post0, long0, bound0, answered0, decoded0⟩ :=
    balanceRead_inv .first fork mem wf firstCall
  have reply0 := balanceReplyMemory_ptr out0 mem
  obtain ⟨guardGas1, secondGuard⟩ := syncSecondRequest_inv fork reply0 decoded0
  obtain ⟨code1, guardGas1', secondCall⟩ := syncCodeGuard_inv .second fork secondGuard
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget) :=
    balanceRequestMemory_ptr reply0 sevm.currentTarget
  obtain ⟨gw1, callGas1, d1, out1, decodedGas1, call1, post1, long1, bound1, answered1, decoded1⟩ :=
    balanceRead_inv .second fork request1 reply0.wf secondCall
  have stor0 : ∀ a, Devm.getStor d0 a = Devm.getStor b a := by
    intro a
    refine (post0.stor a).trans ?_
    unfold temporalAccountAccessBase
    split <;> rfl
  have stor1 : ∀ a, Devm.getStor d1 a = Devm.getStor b a := by
    intro a
    refine (post1.stor a).trans ?_
    have warm : Devm.getStor
        (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr) a =
        Devm.getStor (afterSload sevm d0 7) a := by
      unfold temporalAccountAccessBase
      split <;> rfl
    rw [warm, afterSload_getStor, stor0 a]
  have logs0 : d0.logs = b.logs := by
    refine post0.logs.trans ?_
    unfold temporalAccountAccessBase
    split <;> rfl
  have logs1 : d1.logs = b.logs := by
    refine post1.logs.trans ?_
    have warm : (temporalAccountAccessBase (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).logs =
        (afterSload sevm d0 7).logs := by
      unfold temporalAccountAccessBase
      split <;> rfl
    rw [warm, afterSload_logs, logs0]
  have output0 : d0.output = b.output := by
    refine (post0.output rfl).trans ?_
    unfold temporalAccountAccessBase
    split <;> rfl
  have output1 : d1.output = b.output := by
    refine (post1.output rfl).trans ?_
    have warm : (temporalAccountAccessBase (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).output =
        (afterSload sevm d0 7).output := by
      unfold temporalAccountAccessBase
      split <;> rfl
    rw [warm, afterSload_output, output0]
  exact ⟨gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1, d1, out1, decodedGas1,
    code0, call0, post0, long0, bound0, answered0, decoded0, code1, call1, post1,
    long1, bound1, answered1, stor0, stor1, logs1, output1, decoded1⟩


/-- Exact two-call composition. External premises are the two actual primitive
calls at their derived worlds, with real success flags, gas and answer widths. -/
theorem syncBalancePair_exact {sevm : Sevm} {b d0 d1 : Devm}
    {R : List B256} {M : Mem} {callGas0 callGas1 tailGas : Nat}
    {token0 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget))
    (wf : Mem.Wf M) (room : R.length ≤ 1010)
    (nonzero0 : (b.getCode token0.toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase b token0.toAdr)
        (callGas0.toB256 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
    (returnedGas1 : d1.gasLeft = tailGas + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d1 (Bytes.toB256 (d1.returnData.take 32) :: Bytes.toB256 (d0.returnData.take 32) ::
        0x1fd4 :: tag :: R)
        (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget d1.returnData) tailGas)
      SyncBalanceSite.second.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (token0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget)
        (callGas0 + 5 + 22 + temporalAccountAccessCost b token0.toAdr))
      SyncBalanceSite.first.codeGuardTree o := by
  have reply0 := balanceReplyMemory_ptr d0.returnData mem
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
        sevm.currentTarget) := balanceRequestMemory_ptr reply0 sevm.currentTarget
  apply syncCodeGuard_exact .first fork (by simp only [List.length_cons]; omega) nonzero0
  apply balanceRead_exact .first fork mem wf (by simp only [List.length_cons]; omega)
    call0 success0 returnedGas0 long0
  apply syncSecondRequest_exact fork reply0 room rfl
  apply syncCodeGuard_exact .second fork (by simp only [List.length_cons]; omega) nonzero1
  exact balanceRead_exact .second fork request1 reply0.wf
    (by simp only [List.length_cons]; omega) call1 success1 returnedGas1 long1 body


/-- The literal first request locks slot12, loads token0, and installs the
actual overlapping request before its code guard. The same derivation and
continuation are retained through every primitive step. -/
theorem syncFirstRequest_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {tag : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (tag :: R) M G) t_1e66_c31 seg) :
    sevm.isStatic = false ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (afterSload sevm (afterSstore sevm b 12 0) 6)
          (((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
           ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
           128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
           ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
           0x1fd4 :: tag :: R)
          (balanceRequestMemory M sevm.currentTarget) gas)
        SyncBalanceSite.first.codeGuardTree seg := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by decide)
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have read2 : Bytes.toB256 ((balanceRequestMemory M sevm.currentTarget).read 64 32).1 = 128 :=
    mem2.word
  have same2 : ((balanceRequestMemory M sevm.currentTarget).read 64 32).2 =
      balanceRequestMemory M sevm.currentTarget := mem2.read_self (by decide)
  simp only [balanceRequestMemory, balanceOfSelectorWord] at read2 same2
  unfold t_1e66_c31 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  have mutable := ri_sstore_nonstatic fork (StepIn.toRun hs)
  obtain ⟨_, rfl⟩ := ri_sstore fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read0, same0] at hd; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 128 rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  have hp := of_run_address (StepIn.toRun hs)
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have hd := St.of_stackRel hp
  rw [stack] at hd
  rw [hd] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_mstore_nat 132 rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, read2, same2] at hd; subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  rw [ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨gas, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  exact ⟨mutable, gas, run⟩


/-- The first literal prefix costs126 local gas, including both scratch
expansions, besides the actual selected lock store and token0 read. -/
theorem syncFirstRequest_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G load : Nat} {tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (room : R.length ≤ 1010) (static : sevm.isStatic = false)
    (charge : load = sloadCost sevm (afterSstore sevm b 12 0) 6)
    (sentry : gCallStipend < G + load + 119 + sstoreCost sevm b 12 0)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm (afterSstore sevm b 12 0) 6)
        (((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
         ((afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6).toAdr.toB256 ::
         0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) G)
      SyncBalanceSite.first.codeGuardTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (tag :: R) M (G + sstoreCost sevm b 12 0 + load + 126)) t_1e66_c31 o := by
  have mem1 : PtrMem 128 160 (M.write 128 balanceOfSelectorWord.toBytes) :=
    mem.write 128 balanceOfSelectorWord (Or.inr (by decide))
  have mem2 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  unfold t_1e66_c31
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + sstoreCost sevm b 12 0 + load + 119 =
    (G + load + 119) + sstoreCost sevm b 12 0 by omega]
  apply rx_sstore fork sentry static
  apply rx_push (w := 6) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 116 = (G + 116) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem.size]; decide) mem.word
    (mem.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := balanceOfSelectorWord) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 128) (v := balanceOfSelectorWord) (c := 9)
    (by rw [St.extCost_eq mem.size]; decide) rfl
  refine .next (Ninst.runCompiled_pushItem (G := G + 90) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St (afterSload sevm (afterSstore sevm b 12 0) 6)
      (sevm.currentTarget.toB256 :: 128 :: 64 ::
       (afterSstore sevm b 12 0).getStorVal sevm.currentTarget 6 :: tag :: R)
      (M.write 128 balanceOfSelectorWord.toBytes) (G + 90)) _ o
  apply rx_push (w := 4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 132) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 132) (v := sevm.currentTarget.toB256) (c := 6)
    (by rw [St.extCost_eq mem1.size]; decide) rfl
  apply rx_swap1
  apply rx_mload (i := 64) (v := 128) (c := 3)
    (by rw [St.extCost_eq mem2.size]; decide) mem2.word
    (mem2.read_self (by decide)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1fd4) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_push (w := ~~~ addressMask) ff20_eq (by simp only [List.length_cons]; omega)
  apply rx_and (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons]; omega)
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
  exact body


/-- Successful entry into the lock-protected callee reads slot12 and selects
the actual unlocked arm, retaining that read's warming metadata. -/
theorem syncLockGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {tag : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (tag :: R) M G) t_1df5_c31 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ ∃ gas,
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (afterSload sevm b 12) (tag :: R) M gas) t_1e66_c31 seg := by
  unfold t_1df5_c31 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, gas, body⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_1e00_c31.noOk = true))
  · change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
    have unlocked : b.getStorVal sevm.currentTarget 12 = 1 := by
      by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
      · exact eq.symm
      · simp only [B256.eqCheck, eq, ite_false] at accepted
        exact False.elim (accepted rfl)
    exact ⟨unlocked, gas, body⟩

/-- The lock guard has23 local gas in addition to its selected slot12 read. -/
theorem syncLockGuard_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1010)
    (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (charge : load = sloadCost sevm b 12)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 12) (tag :: R) M G) t_1e66_c31 o) :
    SFunc.RunExact cert.prog sevm (St b (tag :: R) M (G + load + 23)) t_1df5_c31 o := by
  unfold t_1df5_c31
  apply rx_dest
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  rw [show G + load + 19 = (G + 19) + load by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_eq (v := 1) (by rw [unlocked]; decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1e66) rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) body


/-- The actual entry read and lock write before either external observation. -/
def syncLockedWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 12) 12 0

def syncFirstWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (syncLockedWorld sevm b) 6

def syncFirstToken (sevm : Sevm) (b : Devm) : B256 :=
  ((syncLockedWorld sevm b).getStorVal sevm.currentTarget 6).toAdr.toB256

/-- The complete successful sync callee derives its lock and balance guards
from actual bytes. Both call witnesses, full answers and decoded continuation
are retained before the actual shared update and unlock result. -/
theorem syncCallee_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b (tag :: R) M G) t_1df5_c31 o) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes) (decodedGas0 : Nat)
      (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (decodedGas1 finalGas : Nat),
      let u0 := syncFirstWorld sevm b
      let token0 := syncFirstToken sevm b
      let w0 := temporalAccountAccessBase u0 token0.toAdr
      let M0 := balanceReplyMemory M sevm.currentTarget out0
      let balance0 := Bytes.toB256 (out0.take 32)
      let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
      let u1 := afterSload sevm d0 7
      let w1 := temporalAccountAccessBase u1 token1.toAdr
      (u0.getCode token0.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
          (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
      StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2^256 ∧
      StaticAnswered sevm w0 token0.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d0 (balance0 :: 0x1fd4 :: tag :: R) M0 decodedGas0)
        SyncBalanceSite.first.afterDecodeTree (.done o) ∧
      (u1.getCode token1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm
        (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
          (balanceRequestMemory M0 sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost w1 d1 (164 :: 0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2^256 ∧
      StaticAnswered sevm w1 token1.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      (∀ a, Devm.getStor d0 a = Devm.getStor u0 a) ∧
      (∀ a, Devm.getStor d1 a = Devm.getStor u0 a) ∧
      d1.logs = b.logs ∧ d1.output = b.output ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d1 (Bytes.toB256 (out1.take 32) :: balance0 :: 0x1fd4 :: tag :: R)
          (balanceReplyMemory M0 sevm.currentTarget out1) decodedGas1)
        SyncBalanceSite.second.afterDecodeTree (.done o) ∧
      balance0.toNat < 2 ^ 112 ∧ (Bytes.toB256 (out1.take 32)).toNat < 2 ^ 112 ∧
      o = .returned (St (syncResultWorld sevm d1 balance0 (Bytes.toB256 (out1.take 32))) R
        (syncResultMemory sevm d1 (balanceReplyMemory M0 sevm.currentTarget out1)
          balance0 (Bytes.toB256 (out1.take 32))) finalGas) := by
  obtain ⟨unlocked, _, request⟩ := syncLockGuard_inv fork (SFunc.runP_iff_runCutP_nil.mp run)
  obtain ⟨mutable, _, firstGuard⟩ := syncFirstRequest_inv fork mem request
  have requestMem : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  obtain ⟨gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1, d1, out1, decodedGas1,
    code0, call0, post0, long0, bound0, answered0, decoded0, code1, call1, post1,
    long1, bound1, answered1, stor0, stor1, logs1, output1, decoded1⟩ :=
    syncBalancePair_inv fork requestMem mem.wf firstGuard
  have reply0 := balanceReplyMemory_ptr out0 requestMem
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget) :=
    balanceRequestMemory_ptr reply0 sevm.currentTarget
  have reply1 := balanceReplyMemory_ptr out1 request1
  have decodedRun : SFunc.Run cert.prog sevm
      (St d1 (Bytes.toB256 (out1.take 32) :: Bytes.toB256 (out0.take 32) :: 0x1fd4 :: tag :: R)
        (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1)
        decodedGas1) SyncBalanceSite.second.afterDecodeTree o :=
    (SFunc.runP_iff_runCutP_nil.mpr decoded1).mono StepIn.toRun
  obtain ⟨balanceBound0, balanceBound1, _, finalGas, result⟩ :=
    syncUpdateUnlock_inv fork reply1 decodedRun
  have logs : d1.logs = b.logs := by
    rw [logs1, afterSload_logs, afterSstore_logs, afterSload_logs]
  have output : d1.output = b.output := by
    rw [output1, afterSload_output, afterSstore_output, afterSload_output]
  exact ⟨unlocked, mutable, gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1,
    d1, out1, decodedGas1, finalGas, code0, call0, post0, long0, bound0, answered0,
    decoded0, code1, call1, post1, long1, bound1, answered1, stor0, stor1, logs,
    output, decoded1, balanceBound0, balanceBound1, result⟩


/-- The actual entry lock preserves every foreign-account key and every
selected Pair key except its lock slot. -/
theorem syncFirstWorld_storage_frame {sevm : Sevm} {b : Devm} {a : Adr} {k : B256}
    (frame : a ≠ sevm.currentTarget ∨ k ≠ 12) :
    (syncFirstWorld sevm b).getStorVal a k = b.getStorVal a k := by
  unfold syncFirstWorld syncLockedWorld
  rw [getStorVal_afterSload]
  by_cases account : a = sevm.currentTarget
  · subst a
    have key := frame.resolve_left (not_ne_iff.mpr rfl)
    rw [getStorVal_afterStore, Stor.get_set_ne _ (Ne.symm key)]
    rfl
  · change (Devm.getStor _ _).get k = (Devm.getStor _ _).get k
    rw [getStor_afterStore_ne account]

/-- The shared update and concrete unlock preserve all keys outside the four
actual Pair slots, including every key of every other account. -/
theorem syncResultWorld_storage_frame {sevm : Sevm} {b : Devm}
    {balance0 balance1 : B256} {a : Adr} {k : B256}
    (frame : a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 12)) :
    (syncResultWorld sevm b balance0 balance1).getStorVal a k = b.getStorVal a k := by
  unfold syncResultWorld
  by_cases account : a = sevm.currentTarget
  · subst a
    obtain ⟨key8, key9, key10, key12⟩ := frame.resolve_left (not_ne_iff.mpr rfl)
    change (Devm.getStor _ _).get k = _
    rw [afterSstore_getStor_self, Stor.get_set_ne _ (Ne.symm key12)]
    change (syncUpdatedWorld sevm b balance0 balance1).getStorVal sevm.currentTarget k = _
    unfold syncUpdatedWorld
    rw [updateWorld_storage_frame (Or.inr ⟨key8, key9, key10⟩), getStorVal_afterSload]
  · change (Devm.getStor _ _).get k = _
    rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm account)]
    change (syncUpdatedWorld sevm b balance0 balance1).getStorVal a k = _
    unfold syncUpdatedWorld
    rw [updateWorld_storage_frame (Or.inl account), getStorVal_afterSload]


/-- Both actual primitive calls, their successful full-response posts and
decoder continuations occur in the same certified callee derivation. -/
def SyncPrimitiveCallPair (D : Exec.Deriv) (sevm : Sevm) (b : Devm)
    (M : Mem) (R : List B256) (tag : B256) (d0 d1 : Devm)
    (out0 out1 : Bytes) (o : Outcome) : Prop :=
  ∃ (gw0 : B256) (gas0 decoded0 : Nat) (gw1 : B256) (gas1 decoded1 : Nat),
    let token0 := syncFirstToken sevm b
    let token1 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256
    let w0 := temporalAccountAccessBase (syncFirstWorld sevm b) token0.toAdr
    let w1 := temporalAccountAccessBase (afterSload sevm d0 7) token1.toAdr
    let M0 := balanceReplyMemory M sevm.currentTarget out0
    let balance0 := Bytes.toB256 (out0.take 32)
    ((syncFirstWorld sevm b).getCode token0.toAdr).size.toB256 ≠ 0 ∧
    StepIn D sevm
      (St w0 (gw0 :: token0 :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) gas0) (.exec .staticcall) d0 ∧
    StaticCallPost w0 d0 (164 :: 0x70a08231 :: token0 :: 0x1fd4 :: tag :: R)
      (balanceRequestMemory M sevm.currentTarget) 128 36 128 32 1 out0 ∧
    SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d0 (balance0 :: 0x1fd4 :: tag :: R) M0 decoded0)
      SyncBalanceSite.first.afterDecodeTree (.done o) ∧
    ((afterSload sevm d0 7).getCode token1.toAdr).size.toB256 ≠ 0 ∧
    StepIn D sevm
      (St w1 (gw1 :: token1 :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M0 sevm.currentTarget) gas1) (.exec .staticcall) d1 ∧
    StaticCallPost w1 d1 (164 :: 0x70a08231 :: token1 :: balance0 :: 0x1fd4 :: tag :: R)
      (balanceRequestMemory M0 sevm.currentTarget) 128 36 128 32 1 out1 ∧
    SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d1 (Bytes.toB256 (out1.take 32) :: balance0 :: 0x1fd4 :: tag :: R)
        (balanceReplyMemory M0 sevm.currentTarget out1) decoded1)
      SyncBalanceSite.second.afterDecodeTree (.done o)


/-- The actual successful callee supplies the arbitrary ordered observations
used by the source update. Entry-field correspondence is transported through
the concrete lock and both primitive static posts; no endpoint is assumed. -/
theorem syncCalleeSourceCalls_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {tag : B256} {o : Outcome}
    {st : State} {ctx : Context}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = st.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = st.token1)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b (tag :: R) M G) t_1df5_c31 o) :
    ∃ (d0 d1 : Devm) (out0 out1 : Bytes) (gas : Nat) (post : State)
      (event : Event) (oracle : OracleUpdate),
      let balance0 := Bytes.toB256 (out0.take 32)
      let balance1 := Bytes.toB256 (out1.take 32)
      let result := syncResultWorld sevm d1 balance0 balance1
      StaticAnswered sevm (temporalAccountAccessBase (syncFirstWorld sevm b) st.token0)
        st.token0 (ExternalOperation.encode (.balanceOf ctx.pair)) out0 ∧
      StaticAnswered sevm (temporalAccountAccessBase (afterSload sevm d0 7) st.token1)
        st.token1 (ExternalOperation.encode (.balanceOf ctx.pair)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      st.update ctx balance0 balance1 st.reserve0.val st.reserve1.val = .ok (post, event, oracle) ∧
      ReserveSlotMatches { post with unlocked := 1 } sevm result ∧
      result.getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      result.getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      result.getStorVal sevm.currentTarget 12 = 1 ∧
      event = .sync balance0.toNat balance1.toNat ∧
      result.logs = b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] ∧
      (∀ a k, a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 12) →
        result.getStorVal a k = b.getStorVal a k) ∧
      result.output = b.output ∧
      o = .returned (St result R
        (syncResultMemory sevm d1
          (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1)
          balance0 balance1) gas) ∧
      SyncPrimitiveCallPair D sevm b M R tag d0 d1 out0 out1 o := by
  obtain ⟨_, _, gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1, d1, out1,
    decodedGas1, gas, code0, call0, post0, long0, bound0, answered0, decoded0,
    code1, call1, post1, long1, bound1, answered1, stor0, stor1, logs1, output1,
    decoded1, balanceBound0, balanceBound1, result⟩ := syncCallee_inv fork mem run
  have selected (k : B256) (key : k ≠ 12) :
      d1.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k := by
    change (Devm.getStor _ _).get k = _
    rw [stor1 sevm.currentTarget]
    exact syncFirstWorld_storage_frame (Or.inr key)
  have slots1 : ReserveSlotMatches st sevm d1 := by
    simpa only [ReserveSlotMatches, selected 8 (by decide)] using slots
  obtain ⟨post, event, oracle, source, reserves, price0, price1, lock, sync, logs⟩ :=
    syncUpdateSource_result slots1 (by rw [selected 9 (by decide)]; exact cum0)
      (by rw [selected 10 (by decide)]; exact cum1) time pair balanceBound0 balanceBound1
  have firstToken : (syncFirstToken sevm b).toAdr = st.token0 := by
    unfold syncFirstToken
    rw [toAdr_toB256]
    unfold syncLockedWorld
    rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (12 : B256) ≠ 6)]
    exact token0
  have secondToken : (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = st.token1 := by
    rw [toAdr_toB256]
    have slot0 := congrArg (fun storage : Stor => storage.get (7 : B256)) (stor0 sevm.currentTarget)
    change d0.getStorVal sevm.currentTarget 7 = (syncFirstWorld sevm b).getStorVal sevm.currentTarget 7 at slot0
    rw [slot0, syncFirstWorld_storage_frame (Or.inr (by decide : (7 : B256) ≠ 12))]
    exact token1
  have output : (syncResultWorld sevm d1 (Bytes.toB256 (out0.take 32))
      (Bytes.toB256 (out1.take 32))).output = b.output := by
    unfold syncResultWorld syncUpdatedWorld
    rw [afterSstore_output, updateWorld_output, afterSload_output, output1]
  refine ⟨d0, d1, out0, out1, gas, post, event, oracle, ?_, ?_, long0, bound0,
    long1, bound1, source, reserves, price0, price1, lock, sync, ?_, ?_, output, result, ?_⟩
  · simpa only [firstToken, pair] using answered0
  · simpa only [secondToken, pair] using answered1
  · rw [logs, logs1]
  · intro a k frame
    rw [syncResultWorld_storage_frame frame]
    change (Devm.getStor d1 a).get k = _
    rw [stor1 a]
    exact syncFirstWorld_storage_frame (frame.imp_right (fun h => h.2.2.2))
  · exact ⟨gw0, callGas0, decodedGas0, gw1, callGas1, decodedGas1,
      code0, call0, post0, decoded0, code1, call1, post1, decoded1⟩

theorem syncCalleeSource_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {tag : B256} {o : Outcome}
    {st : State} {ctx : Context}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = st.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = st.token1)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b (tag :: R) M G) t_1df5_c31 o) :
    ∃ (d0 d1 : Devm) (out0 out1 : Bytes) (gas : Nat) (post : State)
      (event : Event) (oracle : OracleUpdate),
      let balance0 := Bytes.toB256 (out0.take 32)
      let balance1 := Bytes.toB256 (out1.take 32)
      let result := syncResultWorld sevm d1 balance0 balance1
      StaticAnswered sevm (temporalAccountAccessBase (syncFirstWorld sevm b) st.token0)
        st.token0 (ExternalOperation.encode (.balanceOf ctx.pair)) out0 ∧
      StaticAnswered sevm (temporalAccountAccessBase (afterSload sevm d0 7) st.token1)
        st.token1 (ExternalOperation.encode (.balanceOf ctx.pair)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      st.update ctx balance0 balance1 st.reserve0.val st.reserve1.val = .ok (post, event, oracle) ∧
      ReserveSlotMatches { post with unlocked := 1 } sevm result ∧
      result.getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      result.getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      result.getStorVal sevm.currentTarget 12 = 1 ∧
      event = .sync balance0.toNat balance1.toNat ∧
      result.logs = b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] ∧
      (∀ a k, a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 12) →
        result.getStorVal a k = b.getStorVal a k) ∧
      result.output = b.output ∧
      o = .returned (St result R
        (syncResultMemory sevm d1
          (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget out0) sevm.currentTarget out1)
          balance0 balance1) gas) := by
  obtain ⟨d0, d1, out0, out1, gas, post, event, oracle,
    answered0, answered1, long0, bound0, long1, bound1, source, reserves,
    price0, price1, lock, sync, logs, frame, output, result, _⟩ :=
    syncCalleeSourceCalls_inv fork mem slots cum0 cum1 token0 token1 time pair run
  exact ⟨d0, d1, out0, out1, gas, post, event, oracle,
    answered0, answered1, long0, bound0, long1, bound1, source, reserves,
    price0, price1, lock, sync, logs, frame, output, result⟩


/-- The public sync wrapper enters the actual callee with its return tag and
then executes the literal STOP suffix. The same derivation predicate remains
on the callee, including both nested static calls. -/
theorem syncEntry_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b R M G) t_067b_c78 o) :
    ∃ calleeGas d finalGas,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St b (0x0257 :: R) M calleeGas) t_1df5_c31 (.returned d) ∧
      o = .halted (St d d.stack d.memory finalGas) := by
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_067b_c78 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  cases h with
  | callHalt dd lookup pop callee =>
    rw [show cert.prog[31]? = some t_1df5_c31 from rfl] at lookup
    cases lookup
    have calleeRun := (St.of_pop1 pop).2 ▸ callee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, result⟩ := syncCallee_inv fork mem calleeRun
    cases result
  | callRet dd lookup pop callee tail =>
    rw [show cert.prog[31]? = some t_1df5_c31 from rfl] at lookup
    cases lookup
    rename_i called returned
    have calleeRun := (St.of_pop1 pop).2 ▸ callee
    unfold t_0257_c78 at tail
    rw [St.self (d := returned) rfl rfl] at tail
    obtain ⟨gas, tail⟩ := ric_destP tail
    cases tail with
    | last stop =>
      have eq := Except.ok.inj stop
      exact ⟨_, _, gas, calleeRun, congrArg Outcome.halted eq.symm⟩


/-- Exact gas before the first callee call, including the actual lock read,
lock write, token0 read, scratch expansion and code guard. -/
def syncCalleePrefixGas (sevm : Sevm) (b : Devm) (callGas0 : Nat) : Nat :=
  (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
      (syncFirstToken sevm b).toAdr + sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 + 126) + sloadCost sevm b 12 + 23

/-- Compose the actual lock/request prefix and both compiled external calls
with the continuation after the second decoder. This prefix theorem leaves
that concrete continuation explicit; it introduces no desired source endpoint. -/
theorem syncCalleePrefix_exact {sevm : Sevm} {b d0 d1 : Devm}
    {R : List B256} {M : Mem} {callGas0 callGas1 tailGas : Nat}
    {tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1010)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: tag :: R)
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
    (returnedGas1 : d1.gasLeft = tailGas + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (body : SFunc.RunExact cert.prog sevm
      (St d1 (Bytes.toB256 (d1.returnData.take 32) :: Bytes.toB256 (d0.returnData.take 32) ::
        0x1fd4 :: tag :: R)
        (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget d1.returnData) tailGas)
      SyncBalanceSite.second.afterDecodeTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (tag :: R) M (syncCalleePrefixGas sevm b callGas0)) t_1df5_c31 o := by
  unfold syncCalleePrefixGas
  apply syncLockGuard_exact fork room unlocked rfl
  apply syncFirstRequest_exact fork mem room static rfl sentry
  exact syncBalancePair_exact fork (balanceRequestMemory_ptr mem sevm.currentTarget) mem.wf room
    nonzero0 call0 success0 returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1 body

/-- Gas of the actual slot-8 extraction, shared update and unlock. The oracle
charges occur only when the shared update takes its accumulator branch. -/
def syncUpdateUnlockGas (sevm : Sevm) (b : Devm) (balance0 balance1 : B256)
    (n headerLoad load9 store9 load10 store10 load8 store8 G : Nat) : Nat :=
  let u := afterSload sevm b 8
  let old0 := reserve0Read (b.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (b.getStorVal sevm.currentTarget 8)
  G + 8 + sstoreCost sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1 + 7 +
    updateSyncGas n + load8 + store8 + 110 +
    (if updateOracleActive sevm u old0 old1 then load9 + store9 + load10 + store10 + 382 else 0) +
    17 + 20 +
    (if updateOraclePrefixWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0
      then 0 else 17) + headerLoad + 75 +
    (if updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
      then 0 else 17) + 60 + sloadCost sevm b 8 + 43

/-- The post-decoder suffix is closed by the actual shared-update theorem,
including the one packed store, conditional oracle writes, Sync log and unlock.
Only selected primitive charges and separate SSTORE sentries are supplied. -/
theorem syncUpdateUnlock_gasExact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    {balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 n M)
    (static : sevm.isStatic = false) (bound0 : balance0.toNat < 2 ^ 112)
    (bound1 : balance1.toNat < 2 ^ 112) (room : R.length ≤ 1007) :
    let u := afterSload sevm b 8
    let old0 := reserve0Read (b.getStorVal sevm.currentTarget 8)
    let old1 := reserve1Read (b.getStorVal sevm.currentTarget 8)
    let finalGas := G + 8 + sstoreCost sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1 + 7
    headerLoad = sloadCost sevm u 8 →
    load8 = sloadCost sevm (updateOracleWorld sevm u old0 old1) 8 →
    store8 = sstoreCost sevm (afterSload sevm (updateOracleWorld sevm u old0 old1) 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1) →
    (updateOracleActive sevm u old0 old1 →
      load9 = sloadCost sevm (afterSload sevm u 8) 9 ∧
      store9 = sstoreCost sevm (afterSload sevm (afterSload sevm u 8) 9) 9
        (updateAccumulatorWord ((afterSload sevm u 8).getStorVal sevm.currentTarget 9)
          (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
      load10 = sloadCost sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
      store10 = sstoreCost sevm (afterSload sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
        (updateAccumulatorWord
          ((updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
            sevm.currentTarget 10) (updatePriceWord old1 old0)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time))) →
    gCallStipend < finalGas + updateSyncGas n + store8 →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas n + load8 + store8 + 110 + store10) →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas n + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) →
    gCallStipend < G + 8 + sstoreCost sevm (syncUpdatedWorld sevm b balance0 balance1) 12 1 →
    SFunc.RunExact cert.prog sevm
      (St b (balance1 :: balance0 :: 0x1fd4 :: tag :: R) M
        (syncUpdateUnlockGas sevm b balance0 balance1 n headerLoad load9 store9 load10 store10 load8 store8 G))
      SyncBalanceSite.second.afterDecodeTree
      (.returned (St (syncResultWorld sevm b balance0 balance1) R
        (syncResultMemory sevm b M balance0 balance1) G)) := by
  dsimp only
  intro headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9 unlockSentry
  unfold syncUpdateUnlockGas
  apply syncUpdateUnlock_exact fork static (by omega) rfl unlockSentry
  exact update_exact fork mem static bound0 bound1
    (by simp only [List.length_cons]; omega)
    headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9


/-- The complete sync callee forward run consumes both actual compiled
calls and the closed update/unlock suffix. No endpoint run is an ENV premise. -/
theorem syncCallee_exact {sevm : Sevm} {b d0 d1 : Devm}
    {R : List B256} {M : Mem} {callGas0 callGas1 G headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    {tag : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1007)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory M sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: tag :: R)
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: tag :: R)
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockGas sevm d1 (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 headerLoad load9 store9 load10 store10 load8 store8 G) + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (bound0 : (Bytes.toB256 (d0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (d1.returnData.take 32)).toNat < 2 ^ 112) :
    let balance0 := (Bytes.toB256 (d0.returnData.take 32))
    let balance1 := (Bytes.toB256 (d1.returnData.take 32))
    let u := afterSload sevm d1 8
    let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
    let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
    let finalGas := G + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
    headerLoad = sloadCost sevm u 8 →
    load8 = sloadCost sevm (updateOracleWorld sevm u old0 old1) 8 →
    store8 = sstoreCost sevm (afterSload sevm (updateOracleWorld sevm u old0 old1) 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1) →
    (updateOracleActive sevm u old0 old1 →
      load9 = sloadCost sevm (afterSload sevm u 8) 9 ∧
      store9 = sstoreCost sevm (afterSload sevm (afterSload sevm u 8) 9) 9
        (updateAccumulatorWord ((afterSload sevm u 8).getStorVal sevm.currentTarget 9)
          (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
      load10 = sloadCost sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
      store10 = sstoreCost sevm (afterSload sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
        (updateAccumulatorWord
          ((updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
            sevm.currentTarget 10) (updatePriceWord old1 old0)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time))) →
    gCallStipend < finalGas + updateSyncGas 192 + store8 →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) →
    gCallStipend < G + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
    SFunc.RunExact cert.prog sevm
      (St b (tag :: R) M (syncCalleePrefixGas sevm b callGas0)) t_1df5_c31
      (.returned (St (syncResultWorld sevm d1 balance0 balance1) R
        (syncResultMemory sevm d1
          (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
            sevm.currentTarget d1.returnData) balance0 balance1) G)) := by
  dsimp only
  intro headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9 unlockSentry
  have request0 : PtrMem 128 192 (balanceRequestMemory M sevm.currentTarget) :=
    balanceRequestMemory_ptr mem sevm.currentTarget
  have reply0 := balanceReplyMemory_ptr d0.returnData request0
  have request1 : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
        sevm.currentTarget) := balanceRequestMemory_ptr reply0 sevm.currentTarget
  have reply1 := balanceReplyMemory_ptr d1.returnData request1
  apply syncCalleePrefix_exact fork mem (by omega) static unlocked sentry nonzero0 call0 success0
    returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1
  exact syncUpdateUnlock_gasExact fork reply1 static bound0 bound1 room
    headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9 unlockSentry

/-- The literal sync selector follows the actual dispatcher to its wrapper.
Every cut step keeps the instruction provenance from the same raw derivation. -/
theorem syncSelector_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.RunP (StepIn D) cert.prog sevm (St b [0xfff6cae9] M G') t_067b_c78 o := by
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_calldataload hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd⟩ := ri_shr hd.toRun
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0xfff6cae9 : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_002b_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_0036_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gtP StepIn.toRun h
  simp only [show B256.gtCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_0041_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eqP (g := t_05da_c75) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_004c_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eqP (g := t_05e2_c76) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xd5, 0x05, 0xac, 0xcf])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_0057_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_eqP (g := t_0640_c77) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xdd, 0x62, 0xed, 0x3e])
    (0xfff6cae9 : B256) = 0 from by decide, ite_true] at h
  unfold t_0062_c0 at h
  obtain ⟨gas, h⟩ := ric_cmp_eqP (g := t_067b_c78) StepIn.toRun (by decide) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0xff, 0xf6, 0xca, 0xe9])
    (0xfff6cae9 : B256) = 1 from by decide,
    show ¬ ((1 : B256) = 0) from by decide, ite_false] at h
  exact ⟨gas, SFunc.runP_iff_runCutP_nil.mpr h⟩


/-- Reuse the public guard facts and retain the original instruction relation
through the same actual scratch/value/size prefix. -/
theorem syncGuards_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {G : Nat} {o : Outcome}
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ G', SFunc.RunP (StepIn D) cert.prog sevm
        (St b [] getterInitMemory G') t_001a_c0 o := by
  obtain ⟨value, size, _, _⟩ := getter_guards_inv (run.mono StepIn.toRun)
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_0000_c0 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd⟩ := ri_mstore hd.toRun
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    show Bytes.toB256 [0x80] = (128 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_callvalue hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero hd.toRun
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
  rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, h⟩
  · simp only [value, B256.eqCheck, ite_true] at zero
    exact ((by decide : (1 : B256) ≠ 0) zero).elim
  · rw [value] at h
    unfold t_0010_c0 at h
    obtain ⟨_, h⟩ := ric_destP h
    obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop hd.toRun
    obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_calldatasize hd.toRun
    obtain ⟨d, hd, h⟩ := ric_nextP h
    obtain ⟨_, hd⟩ := ri_lt hd.toRun
    simp only [show Bytes.toB256 [0x04] = (4 : B256) from rfl] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push hd.toRun
    rcases ric_branchP h with ⟨_, gas, h⟩ | ⟨nonzero, _, _⟩
    · exact ⟨value, size, gas, SFunc.runP_iff_runCutP_nil.mpr h⟩
    · have zero : B256.ltCheck sevm.data.length.toB256 4 = 0 := by
        simp only [B256.ltCheck, not_lt.mpr size, ite_false]
      exact (nonzero zero).elim

/-- The real pc-zero sync run reaches its callee through the public guards,
selector and wrapper, retaining the same raw derivation for both child calls. -/
theorem syncPc0_inv {D : Exec.Deriv} {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : SProg.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ calleeGas d finalGas,
        SFunc.RunP (StepIn D) cert.prog sevm
          (St b [0x0257, 0xfff6cae9] getterInitMemory calleeGas) t_1df5_c31 (.returned d) ∧
        post = St d d.stack d.memory finalGas := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := syncGuards_inv run
  obtain ⟨_, run⟩ := syncSelector_inv selector run
  obtain ⟨calleeGas, d, finalGas, callee, result⟩ := syncEntry_inv fork getterInitMemory_ptr run
  exact ⟨value, size, calleeGas, d, finalGas, callee, Outcome.halted.inj result⟩


/-- The actual sync selector dispatcher costs166 gas after the public guards. -/
theorem syncSelector_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (body : SFunc.RunExact cert.prog sevm (St b [0xfff6cae9] M G) t_067b_c78 o) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + 166)) t_001a_c0 o := by
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_shr (v := 0xfff6cae9) selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xf9) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_002b_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xba9a7a56) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x97) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_0036_c0
  apply rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0xd21220a7) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_push (w := 0x71) rfl (by simp only [List.length_cons, List.length_nil]; decide)
  apply rx_branch_zero
  unfold t_0041_c0
  apply cmp_miss (by decide)
  unfold t_004c_c0
  apply cmp_miss (by decide)
  unfold t_0057_c0
  apply cmp_miss (by decide)
  unfold t_0062_c0
  exact cmp_hit (tgt := t_067b_c78) rfl (by rfl) body

/-- The actual public guard and sync selector route costs229 gas, with the
existing scratch initialization and no imposed upper calldata-size premise. -/
theorem syncDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (body : SFunc.RunExact cert.prog sevm (St b [0xfff6cae9] getterInitMemory G) t_067b_c78 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 229)) t_0000_c0 o := by
  exact getterString_guards_exact value size (syncSelector_exact selector body)

/-- The wrapper adds15 gas before the callee and one gas for the final
JUMPDEST; STOP preserves all returned raw fields except that last gas charge. -/
theorem syncEntry_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M M' : Mem}
    {G calleeGas : Nat} (room : R.length ≤ 1021)
    (callee : SFunc.RunExact cert.prog sevm
      (St b (0x0257 :: R) M calleeGas) t_1df5_c31 (.returned (St d R M' (G + 1)))) :
    SFunc.RunExact cert.prog sevm (St b R M (calleeGas + 15)) t_067b_c78
      (.halted (St d R M' G)) := by
  unfold t_067b_c78
  apply rx_dest
  apply rx_push (w := 0x0257) rfl (by omega)
  apply rx_push (w := 0x1df5) rfl (by simp only [List.length_cons]; omega)
  apply rx_callRet rfl callee
  unfold t_0257_c78
  apply rx_dest
  exact rx_stop


/-- Exact pc-zero sync liveness on the certified tree. The ENV is precisely
the two compiled child calls, successful widths/gas and selected primitive
charges/sentries; the whole handler run is constructed from the closed callee. -/
theorem syncPc0_exact {sevm : Sevm} {b d0 d1 : Devm}
    {callGas0 callGas1 G headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (static : sevm.isStatic = false) (unlocked : b.getStorVal sevm.currentTarget 12 = 1)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
        (syncFirstToken sevm b).toAdr) + sloadCost sevm (syncLockedWorld sevm b) 6 + 119 +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm b).getCode (syncFirstToken sevm b).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockGas sevm d1 (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 headerLoad load9 store9 load10 store10 load8 store8 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (bound0 : (Bytes.toB256 (d0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (d1.returnData.take 32)).toNat < 2 ^ 112) :
    let balance0 := (Bytes.toB256 (d0.returnData.take 32))
    let balance1 := (Bytes.toB256 (d1.returnData.take 32))
    let u := afterSload sevm d1 8
    let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
    let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
    let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
    headerLoad = sloadCost sevm u 8 →
    load8 = sloadCost sevm (updateOracleWorld sevm u old0 old1) 8 →
    store8 = sstoreCost sevm (afterSload sevm (updateOracleWorld sevm u old0 old1) 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1) →
    (updateOracleActive sevm u old0 old1 →
      load9 = sloadCost sevm (afterSload sevm u 8) 9 ∧
      store9 = sstoreCost sevm (afterSload sevm (afterSload sevm u 8) 9) 9
        (updateAccumulatorWord ((afterSload sevm u 8).getStorVal sevm.currentTarget 9)
          (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
      load10 = sloadCost sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
      store10 = sstoreCost sevm (afterSload sevm
        (updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
        (updateAccumulatorWord
          ((updateAccumulatorPost sevm (afterSload sevm u 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
            sevm.currentTarget 10) (updatePriceWord old1 old0)
          (updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time))) →
    gCallStipend < finalGas + updateSyncGas 192 + store8 →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
    (updateOracleActive sevm u old0 old1 →
      gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) →
    gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
    SProg.RunExact cert.prog sevm
      (St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229))
      (St (syncResultWorld sevm d1 balance0 balance1) [0xfff6cae9]
        (syncResultMemory sevm d1
          (balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
            sevm.currentTarget d1.returnData) balance0 balance1) G) := by
  dsimp only
  intro headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9 unlockSentry
  refine ⟨t_0000_c0, rfl, ?_⟩
  apply syncDispatch_exact value size selector
  apply syncEntry_exact (by decide)
  exact syncCallee_exact fork getterInitMemory_ptr (by decide) static unlocked sentry nonzero0
    call0 success0 returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1 bound0 bound1
    headerCharge packedLoadCharge packedStoreCharge oracleCharges sentry8 sentry10 sentry9 unlockSentry



/-- The certified raw pc0 execution supplies the very same derivation to the
public guards, selector, wrapper and callee. No call provenance is erased. -/
theorem sync_raw_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ calleeGas d finalGas,
        SFunc.RunP (StepIn ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
          cert.prog sevm (St b [0x0257, 0xfff6cae9] getterInitMemory calleeGas)
          t_1df5_c31 (.returned d) ∧
        post = St d d.stack d.memory finalGas := by
  exact syncPc0_inv fork selector (lift_sound_in cert_check codeEq fork run)



/-- The source lock preserves the invocation checkpoint and captures reserves
before either external observation. -/
def syncSourceLockedFrame (current : Checkpoint) (ctx : Context) : Frame :=
  { Frame.enter current ctx .sync with
    current := { current with state := { current.state with unlocked := 0 } } }

theorem sync_startTyped_suspended {current : Checkpoint} {ctx : Context}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1) :
    startTyped current ctx .sync =
      .suspended (syncSourceLockedFrame current ctx)
        (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
        (.syncBalance0 current.state.cachedReserves) := by
  have opened : (Frame.enter current ctx .sync).lock =
      .ok (syncSourceLockedFrame current ctx) := by
    simp only [Frame.lock, Frame.enter, unlocked, nonstatic, ite_true, Bool.false_eq_true,
      ite_false, syncSourceLockedFrame]
  simp only [startTyped, startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
    getterResult, opened, Frame.suspend]
  rfl

/-- The first full successful answer advances the actual source segment and
requests token1 from the current checkpoint, retaining the entry reserve cache. -/
theorem sync_resumeBalance0 {frame : Frame} {reserves : CachedReserves}
    {result : ExternalResult}
    (codeExists : result.codeExists = true) (success : result.success = true)
    (long : 32 ≤ result.returndata.length) :
    let request := requestFor .syncBalance0 frame.current.state.token0
      (.balanceOf frame.context.pair)
    resumeSegment frame request (.syncBalance0 reserves) result =
      .suspended (frame.beginResume request)
        (requestFor .syncBalance1 frame.current.state.token1 (.balanceOf frame.context.pair))
        (.syncBalance1 reserves (Bytes.toB256 (result.returndata.take 32))) := by
  simp only [resumeSegment, decodeExternal, requestFor, codeExists, success,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    ite_eq_left long, Frame.suspend, Frame.beginResume]

/-- The source update appends its owned log and oracle receipt at the actual
resumption origin, then restores the lock. -/
def syncSourceUpdatedFrame (frame : Frame) (post : State) (event : Event)
    (oracle : OracleUpdate) : Frame :=
  { frame.withUpdate post event oracle with
    current := { (frame.withUpdate post event oracle).current with
      state := { post with unlocked := 1 } } }

theorem sync_finishUpdated {frame : Frame} {reserves : CachedReserves}
    {balance0 balance1 : B256} {post : State} {event : Event} {oracle : OracleUpdate}
    (updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val = .ok (post, event, oracle)) :
    frame.finishUpdated balance0 balance1 reserves false none [] =
      .finished (syncSourceUpdatedFrame frame post event oracle) [] := by
  rw [Frame.finishUpdated, updated]
  simp only [Bool.false_eq_true, ite_false, Frame.finishLocked, Frame.withEvents,
    Frame.finish, syncSourceUpdatedFrame, Frame.withUpdate, List.map_nil, List.append_nil]

/-- The second full answer consumes the reviewed source update; its oracle
origin is the second resumption, independent of either nested turn count. -/
theorem sync_resumeBalance1 {frame : Frame} {reserves : CachedReserves}
    {balance0 : B256} {result : ExternalResult} {post : State}
    {event : Event} {oracle : OracleUpdate}
    (codeExists : result.codeExists = true) (success : result.success = true)
    (long : 32 ≤ result.returndata.length)
    (updated : frame.current.state.update frame.context balance0
      (Bytes.toB256 (result.returndata.take 32))
      reserves.reserve0.val reserves.reserve1.val = .ok (post, event, oracle)) :
    let request := requestFor .syncBalance1 frame.current.state.token1
      (.balanceOf frame.context.pair)
    resumeSegment frame request (.syncBalance1 reserves balance0) result =
      .finished (syncSourceUpdatedFrame (frame.beginResume request) post event oracle) [] := by
  simp only [resumeSegment, decodeExternal, requestFor, codeExists, success,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    ite_eq_left long]
  apply sync_finishUpdated
  exact updated



/-- Every recursively exact balance-call turn queue retains the source frame.
Successful static Pair views remain in the queue and retain their returns. -/
theorem syncBalanceTurns_frame {frame : Frame} {site : CallSite} {target : Adr}
    {turn : Nat} {turns : Transcript} {executed : TurnsResult}
    (during : ExactTurns frame
      (requestFor site target (.balanceOf frame.context.pair)) turn turns executed) :
    executed.frame = frame := by
  rw [← ExactTurns.realizes during (turns.work + 1) (Nat.le_refl _)]
  apply driveTurns_static_frame
  simp only [externalStatic, requestFor, BEq.rfl, Bool.or_true]



/-- The source continuation after the first balance response has advanced once. -/
def syncSourceSecondFrame (current : Checkpoint) (ctx : Context) : Frame :=
  (syncSourceLockedFrame current ctx).beginResume
    (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))

/-- Two actual recursively exact turn queues and two full successful responses
consume the source handler. Completion and the ordered child-return list are
conclusions; neither is supplied as a desired driver endpoint. -/
theorem sync_source_exact_consumption {current : Checkpoint} {ctx : Context}
    {result0 result1 : ExternalResult} {turns0 turns1 : Transcript}
    {executed0 executed1 : TurnsResult} {post : State} {event : Event}
    {oracle : OracleUpdate}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1)
    (code0 : result0.codeExists = true) (success0 : result0.success = true)
    (long0 : 32 ≤ result0.returndata.length)
    (code1 : result1.codeExists = true) (success1 : result1.success = true)
    (long1 : 32 ≤ result1.returndata.length)
    (during0 : ExactTurns (syncSourceLockedFrame current ctx)
      (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
      0 turns0 executed0)
    (during1 : ExactTurns (syncSourceSecondFrame current ctx)
      (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair))
      0 turns1 executed1)
    (updated : (syncSourceSecondFrame current ctx).current.state.update ctx
      (Bytes.toB256 (result0.returndata.take 32))
      (Bytes.toB256 (result1.returndata.take 32))
      current.state.reserve0.val current.state.reserve1.val = .ok (post, event, oracle)) :
    ExactConsumes (startTyped current ctx .sync)
      (.next result0 turns0 (.next result1 turns1 .done))
      { status := .success [],
        frame := syncSourceUpdatedFrame
          ((syncSourceSecondFrame current ctx).beginResume
            (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)))
          post event oracle,
        remaining := .done,
        childReturns := executed0.childReturns ++ executed1.childReturns } := by
  let frame0 := syncSourceLockedFrame current ctx
  let frame1 := syncSourceSecondFrame current ctx
  let request0 := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
  let request1 := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
  have kept0 : executed0.frame = frame0 := syncBalanceTurns_frame during0
  have kept1 : executed1.frame = frame1 := syncBalanceTurns_frame during1
  have resumed0 :
      resumeSegment frame0 request0 (.syncBalance0 current.state.cachedReserves) result0 =
        .suspended frame1 request1
          (.syncBalance1 current.state.cachedReserves (Bytes.toB256 (result0.returndata.take 32))) :=
    sync_resumeBalance0 code0 success0 long0
  have resumed1 :
      resumeSegment frame1 request1
        (.syncBalance1 current.state.cachedReserves (Bytes.toB256 (result0.returndata.take 32))) result1 =
        .finished (syncSourceUpdatedFrame (frame1.beginResume request1) post event oracle) [] :=
    sync_resumeBalance1 code1 success1 long1 updated
  have terminal := ExactConsumes.finished
    (syncSourceUpdatedFrame (frame1.beginResume request1) post event oracle) []
  rw [← resumed1] at terminal
  have second := ExactConsumes.nextCall
    (frame := frame1) (request := request1)
    (continuation := .syncBalance1 current.state.cachedReserves
      (Bytes.toB256 (result0.returndata.take 32)))
    (result := result1)
    (by simp only [request1, requestFor, code1, Bool.not_true, Bool.and_false])
    (by intro absent; rw [code1] at absent; cases absent)
    during1
    (by simpa only [success1, ite_true, kept1] using terminal)
  rw [← resumed0] at second
  have first := ExactConsumes.nextCall
    (frame := frame0) (request := request0)
    (continuation := .syncBalance0 current.state.cachedReserves) (result := result0)
    (by simp only [request0, requestFor, code0, Bool.not_true, Bool.and_false])
    (by intro absent; rw [code0] at absent; cases absent)
    during0
    (by simpa only [success0, ite_true, kept0] using second)
  rw [sync_startTyped_suspended value nonstatic unlocked]
  simpa only [List.append_nil] using first



/-- The lock changes only the lock field of the accepted update result; it
does not change its cached reserves, modular oracle calculation or event. -/
theorem sync_source_update_locked {st : State} {ctx : Context}
    {balance0 balance1 : B256} {old0 old1 : Nat}
    {post : State} {event : Event} {oracle : OracleUpdate}
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112)
    (updated : st.update ctx balance0 balance1 old0 old1 = .ok (post, event, oracle)) :
    ({ st with unlocked := 0 } : State).update ctx balance0 balance1 old0 old1 =
      .ok ({ post with unlocked := 0 }, event, oracle) := by
  simp only [State.update, dite_eq_left bound0, dite_eq_left bound1] at updated ⊢
  have fields := Except.ok.inj updated
  simp only [Prod.mk.injEq] at fields
  obtain ⟨rfl, rfl, rfl⟩ := fields
  rfl



/-- A source response records the full arbitrary bytes authenticated by a
successful guarded balance call. Recovery output is unused by this operation. -/
def syncExternalReply (out : Bytes) : ExternalResult :=
  { success := true, returndata := out, codeExists := true, recoveryOutput := 0 }

/-- Raw successful sync derives source acceptance and authenticates both full
responses with the same primitive call witnesses. Recursive exact turn queues
remain producer obligations, exposed as implications and consumed here. -/
theorem sync_raw_source_handler_inv {current : Checkpoint} {ctx : Context}
    {sevm : Sevm} {b rawPost : Devm} {G : Nat}
    (slots : ReserveSlotMatches current.state sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = current.state.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = current.state.price1CumulativeLast)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = current.state.token1)
    (lockRep : b.getStorVal sevm.currentTarget 12 = current.state.unlocked)
    (valueRep : ctx.value = sevm.value) (staticRep : ctx.isStatic = sevm.isStatic)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok rawPost)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
    sevm.isStatic = false ∧ current.state.unlocked = 1 ∧
    ∃ (d0 d1 : Devm) (out0 out1 : Bytes) (gas finalGas : Nat)
      (post : State) (event : Event) (oracle : OracleUpdate),
      let D : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok rawPost, run⟩
      let balance0 := Bytes.toB256 (out0.take 32)
      let balance1 := Bytes.toB256 (out1.take 32)
      let result := syncResultWorld sevm d1 balance0 balance1
      let called := St result [0xfff6cae9]
        (syncResultMemory sevm d1
          (balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
            sevm.currentTarget out1) balance0 balance1) gas
      SyncPrimitiveCallPair D sevm b getterInitMemory [0xfff6cae9]
        0x0257 d0 d1 out0 out1 (.returned called) ∧
      StaticAnswered sevm
        (temporalAccountAccessBase (syncFirstWorld sevm b) current.state.token0)
        current.state.token0 (ExternalOperation.encode (.balanceOf ctx.pair)) out0 ∧
      StaticAnswered sevm
        (temporalAccountAccessBase (afterSload sevm d0 7) current.state.token1)
        current.state.token1 (ExternalOperation.encode (.balanceOf ctx.pair)) out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      current.state.update ctx balance0 balance1
        current.state.reserve0.val current.state.reserve1.val = .ok (post, event, oracle) ∧
      ReserveSlotMatches { post with unlocked := 1 } sevm result ∧
      result.getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      result.getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      result.getStorVal sevm.currentTarget 12 = 1 ∧
      event = .sync balance0.toNat balance1.toNat ∧
      result.logs = b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] ∧
      (∀ a k, a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 12) →
        result.getStorVal a k = b.getStorVal a k) ∧
      result.output = b.output ∧
      rawPost = St called called.stack called.memory finalGas ∧
      (∀ (turns0 turns1 : Transcript) (executed0 executed1 : TurnsResult),
        ExactTurns (syncSourceLockedFrame current ctx)
          (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
          0 turns0 executed0 →
        ExactTurns (syncSourceSecondFrame current ctx)
          (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair))
          0 turns1 executed1 →
        ExactConsumes (startTyped current ctx .sync)
          (.next (syncExternalReply out0) turns0 (.next (syncExternalReply out1) turns1 .done))
          { status := .success [],
            frame := syncSourceUpdatedFrame
              ((syncSourceSecondFrame current ctx).beginResume
                (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)))
              { post with unlocked := 0 } event oracle,
            remaining := .done,
            childReturns := executed0.childReturns ++ executed1.childReturns }) := by
  obtain ⟨value, size, calleeGas, d, finalGas, callee, raw⟩ :=
    sync_raw_inv codeEq fork selector run
  have guards := syncCallee_inv fork getterInitMemory_ptr callee
  have unlocked : current.state.unlocked = 1 := lockRep.symm.trans guards.1
  have nonstatic : sevm.isStatic = false := guards.2.1
  have contextValue : ctx.value = 0 := valueRep.trans value
  have contextStatic : ctx.isStatic = false := staticRep.trans nonstatic
  obtain ⟨d0, d1, out0, out1, gas, post, event, oracle,
    answered0, answered1, long0, bound0, long1, bound1, source, reserves,
    price0, price1, lock, sync, logs, frame, output, result, calls⟩ :=
    syncCalleeSourceCalls_inv fork getterInitMemory_ptr slots cum0 cum1 token0 token1 time pair callee
  have calledEq := Outcome.returned.inj result
  subst d
  refine ⟨value, size, nonstatic, unlocked, d0, d1, out0, out1, gas, finalGas,
    post, event, oracle, calls, answered0, answered1, long0, bound0, long1, bound1,
    source, reserves, price0, price1, lock, sync, logs, frame, output, raw, ?_⟩
  intro turns0 turns1 executed0 executed1 during0 during1
  have acceptedFields := State.update_supply_reserves source
  have balanceBound0 : (Bytes.toB256 (out0.take 32)).toNat < 2 ^ 112 := by
    rw [← acceptedFields.2.1]
    exact post.reserve0.isLt
  have balanceBound1 : (Bytes.toB256 (out1.take 32)).toNat < 2 ^ 112 := by
    rw [← acceptedFields.2.2]
    exact post.reserve1.isLt
  have lockedUpdate := sync_source_update_locked balanceBound0 balanceBound1 source
  exact sync_source_exact_consumption contextValue contextStatic unlocked
    (by rfl) (by rfl) long0 (by rfl) (by rfl) long1 during0 during1 lockedUpdate


end Blanc.Lift.UniswapV2Pair
