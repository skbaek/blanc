import Blanc.Composition.UniswapV2PairWeth9LiveHistory
import Blanc.Composition.UniswapV2PairWeth9LiveWorld

/-!
# C4(b): the sync liveness row with WETH9's queries discharged (U8d)

`pair_history_sync_live` takes both tokens' `balanceOf(pair)` `STATICCALL` records.  With WETH9 on
one side, that side's record is WETH9's own run: its result and call gas are pinned (`_read`) to
the leg the deployed code determines (`syncWethRead0` / `syncWethRead1`, U8b1), and its premises
are discharged from the history — WETH9's code at the token the Pair loads, WETH9 not a precompile
(`JointCheckpoint.wethNotPrecompile`) — plus the frame's call depth and the leg's gas sentries
(`fits`, `room`).  What stays is the other token's record and the Pair's own sentries.

* `pair_weth9_history_sync_live_zero` — WETH9 = token0;
* `pair_weth9_history_sync_live_one` — WETH9 = token1.

`SyncLiveOutcome` is `pair_history_sync_live`'s conclusion verbatim (its history premises at `KP`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- `pair_history_sync_live`'s conclusion, verbatim. -/
def SyncLiveOutcome {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop)
    (st₀ : UniswapV2Pair.State) (sevm : Sevm) (pre d0 d1 : Devm) (callGas0 G : Nat) : Prop :=
  ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
    PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      (finish.unlocked = 1 →
        (∃ result, finish.update (writerContext sevm []) (Bytes.toB256 (d0.returnData.take 32))
          (Bytes.toB256 (d1.returnData.take 32)) finish.reserve0.val finish.reserve1.val =
            .ok result) →
        let balance0 := (Bytes.toB256 (d0.returnData.take 32))
        let balance1 := (Bytes.toB256 (d1.returnData.take 32))
        let u := afterSload sevm d1 8
        let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
        let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
        let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
        let h := afterSload sevm u 8
        let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
        let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
        let v := updateOracleWorld sevm u old0 old1
        let store9 := sstoreCost sevm (afterSload sevm h 9) 9
          (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
            (updatePriceWord old0 old1) delta)
        let load10 := sloadCost sevm w9 10
        let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
          (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
            (updatePriceWord old1 old0) delta)
        let load8 := sloadCost sevm v 8
        let store8 := sstoreCost sevm (afterSload sevm v 8) 8
          (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
        gCallStipend < finalGas + updateSyncGas 192 + store8 →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
            load10 + store10 + 42 + 149 + store9) →
        gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
        ∃ (post : Devm)
          (run : Exec 0 sevm (St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229))
            (.ok post)),
          post.gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229),
                .ok post, run⟩ post))

/-! ## The Pair's words and WETH9's code after sync's lock prefix -/

theorem syncLockedWorld_slot {sevm : Sevm} {pre : Devm} {k : B256} (hk : (12 : B256) ≠ k) :
    (syncLockedWorld sevm pre).getStorVal sevm.currentTarget k =
      pre.getStorVal sevm.currentTarget k := by
  change (Devm.getStor (syncLockedWorld sevm pre) sevm.currentTarget).get k =
    (Devm.getStor pre sevm.currentTarget).get k
  unfold syncLockedWorld
  rw [afterSstore_getStor_self, Stor.get_set_ne _ hk, afterSload_getStor]

theorem syncFirstWorld_keeps (sevm : Sevm) (pre : Devm) {w : Adr} (ne : sevm.currentTarget ≠ w) :
    WethKeeps w pre (syncFirstWorld sevm pre) :=
  ((WethKeeps.afterSload sevm pre 12).trans (WethKeeps.afterSstore ne _ 12 0)).trans
    (WethKeeps.afterSload sevm _ 6)

theorem notPrecompile_of_joint {pair weth : Adr} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State} {side : TokenSide} {w : Jaune.State} {sevm : Sevm}
    (joint : JointCheckpoint pair weth K₀ KP st₀ side w) (fork : CoveredFork sevm.benvStat.fork) :
    sevm.benvStat.rules.isPrecomp weth = (false = true) := by
  rw [Bool.false_eq_true]
  exact eq_false (joint.wethNotPrecompile _ fork)

/-- **C4(b), the sync liveness row with WETH9 as token0.**  As `pair_history_sync_live`, from the
joint checkpoint, with WETH9's first `balanceOf(pair)` record removed: its result and call gas are
pinned to `syncWethRead0`.  What stays is token1's record, the frame's call depth, the leg's gas
sentries and the Pair's own sentry. -/
theorem pair_weth9_history_sync_live_zero {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .zero checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (_read : (d0, callGas0) = syncWethRead0 sevm pre callGas1)
    (fits : callGas0 < 2 ^ 256)
    (room : balUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (wethBalanceSkel sevm (syncFirstWorld sevm pre) syncTail
          getterInitMemory 128 (syncFirstToken sevm pre)) +
        balUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128 (syncFirstToken sevm pre)))
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
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
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1
      (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length) :
    SyncLiveOutcome pair trace KP st₀ sevm pre d0 d1 callGas0 G := by
  have h0 : (syncWethRead0 sevm pre callGas1).1 = d0 := (congrArg Prod.fst _read).symm
  have hg : (syncWethRead0 sevm pre callGas1).2 = callGas0 := (congrArg Prod.snd _read).symm
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .zero trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have tok : (syncFirstToken sevm pre).toAdr = weth := by
    unfold syncFirstToken
    rw [toAdr_toB256, syncLockedWorld_slot (by decide), target]
    exact token
  have keeps := syncFirstWorld_keeps sevm pre (w := weth) (target ▸ joint.apart)
  have wcode : (syncFirstWorld sevm pre).state.getCode (syncFirstToken sevm pre).toAdr =
      Weth9.code := by
    rw [tok]
    exact keeps.1.trans code
  have np : sevm.benvStat.rules.isPrecomp (syncFirstToken sevm pre).toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  have spec := syncWethRead0_spec fork depth wcode np (by rw [hg]; exact fits) room
  dsimp only at spec
  rw [h0, hg] at spec
  obtain ⟨nonzero0, call0, success0, returnedGas0, long0, -⟩ := spec
  exact pair_history_sync_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size selector static sentry nonzero0 call0 success0
    returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1

/-- **C4(b), the sync liveness row with WETH9 as token1.**  As `pair_history_sync_live`, from the
joint checkpoint, with WETH9's second `balanceOf(pair)` record removed: its result and call gas
are pinned to `syncWethRead1` over token0's result `d0`.  What stays is token0's record, the
frame's call depth, the leg's gas sentries and the Pair's own sentry. -/
theorem pair_weth9_history_sync_live_one {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .one checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm pre).getCode (syncFirstToken sevm pre).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm pre) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 ::
      [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (_read : (d1, callGas1) = syncWethRead1 sevm d0 G)
    (fits : callGas1 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    SyncLiveOutcome pair trace KP st₀ sevm pre d0 d1 callGas0 G := by
  have h1 : d1 = (syncWethRead1 sevm d0 G).1 := congrArg Prod.fst _read
  have hg : callGas1 = (syncWethRead1 sevm d0 G).2 := congrArg Prod.snd _read
  subst h1 hg
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .one trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have staged := (syncFirstWorld_keeps sevm pre ne).trans
    (WethKeeps.access (w := weth) (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
  have afterX := staged.trans (WethKeeps.staticcall fork call0
    (weth9_code_toList_ne (staged.1.trans code)))
  have slot7 : d0.getStorVal sevm.currentTarget 7 = pre.getStorVal sevm.currentTarget 7 := by
    change (Devm.getStor d0 sevm.currentTarget).get 7 = (Devm.getStor pre sevm.currentTarget).get 7
    rw [compiled_staticcall_stor fork call0, temporalAccountAccessBase_getStor, syncFirstWorld,
      afterSload_getStor]
    exact syncLockedWorld_slot (by decide)
  have tok : (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = weth := by
    rw [toAdr_toB256, slot7, target]
    exact token
  have wcode : (afterSload sevm d0 7).state.getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = Weth9.code := by
    rw [tok]
    exact ((afterX.trans (WethKeeps.afterSload sevm d0 7)).1).trans code
  have np : sevm.benvStat.rules.isPrecomp
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  obtain ⟨nonzero1, call1, success1, returnedGas1, long1, -⟩ :=
    syncWethRead1_spec fork depth wcode np fits room
  exact pair_history_sync_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size selector static sentry nonzero0 call0 success0
    returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1

end Blanc.Composition.UniswapV2PairWeth9Joint
