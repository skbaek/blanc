import Blanc.Lift.UniswapV2Pair.BalanceCallWalk
import Blanc.Lift.CodeSizeWalk

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

end Blanc.Lift.UniswapV2Pair
