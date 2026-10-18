import Blanc.Composition.UniswapV2PairUsdcWeth9LegsSync
import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairUsdcWeth9SyncLiveF
import Blanc.Composition.UniswapV2PairWeth9SyncLive
import Blanc.Lift.Usdc.HistoryEnd

/-!
# C6(c): the sync liveness row with both tokens' queries discharged (U9c)

USDC = `token0`, WETH9 = `token1`.  The predecessor's `pair_weth9_history_sync_live_one` takes
token0's `balanceOf(pair)` record as premises; here that record is USDC's own run, pinned (`_read0`)
to `syncUsdcRead0` at the call gas WETH9's pin fixes, and WETH9's pin (`_read1`) reads USDC's result
only through its gas-free skeleton (`syncWethRead1_withGasLeft`).

What a new Pair frame at the history's future world knows about USDC (`pair_usdc_frame`): the Pair's
stored `token0` word is USDC (the WETH9-side walk keeps both tokens), USDC is installed there and its
admin word is the checkpoint's (`usdc_history_end_installed`).  No never-signer premise.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.Weth9Token Blanc.Composition.UsdcLive

/-- USDC's installed runtimes and admin word read only the world's codes and USDC's storage. -/
theorem usdc_world_congr {P : Adr} {w w' : Jaune.State} (code : ∀ a, w'.getCode a = w.getCode a)
    (stor : w'.getStor P = w.getStor P) :
    (Usdc.UsdcInstalled P w → Usdc.UsdcInstalled P w') ∧ Usdc.adminOf w' P = Usdc.adminOf w P := by
  refine ⟨fun inst => ⟨?_, ?_, ?_, ?_, inst.implApart, inst.libApart⟩, ?_⟩
  · rw [code]; exact inst.proxy
  · rw [code]; exact inst.impl
  · rw [code]; exact inst.lib
  · rw [stor]; exact inst.slot
  · unfold Usdc.adminOf; rw [stor]

/-- **What a new Pair frame at the history's future world knows about USDC.**  The Pair's stored
`token0` word is USDC, USDC is installed, and its admin word is the checkpoint's.  The tokens come
from the WETH9-side walk (`pair_token_walk`, which keeps both of the Pair's tokens); USDC's facts
from `usdc_history_end_installed`. -/
theorem pair_usdc_frame {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {pre : Devm} (state : pre.state = future.state) :
    ((pre.getStor pair).get 6).toAdr = usdc ∧ Usdc.UsdcInstalled usdc pre.state ∧
      Usdc.adminOf pre.state usdc = Usdc.adminOf checkpoint.state usdc := by
  obtain ⟨hist1, answerable, start⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  have walk := pair_token_walk (weth9Core weth KW).weak weth9Book_erc20Abi
    (weth9SelfCaller weth KW).weak .one trace (weth9Book_laws.holderLaws weth trace pair)
    joint.weth9.pairCode joint.weth9.pairRep pairFresh hist1 joint.weth9.token
    joint.weth9.unlocked joint.weth9.apart answerable joint.weth9.distinct joint.weth9.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
    (weth9_tokenEntered trace joint.weth9)
  obtain ⟨-, finish, K', replayed⟩ := pair_history_replayed trace joint.weth9.pairCode
    joint.weth9.pairRep pairFresh
  obtain ⟨steps, observed, auth, replay, -⟩ := id replayed
  obtain ⟨-, -, -, -, tokens, -, -⟩ := walk steps replay auth observed (pre := []) (post := [])
    (by rw [List.nil_append, List.append_nil]) (PairClosed.nil pair)
    (settledFrames_pairClosed trace) ⟨rfl, rfl, rfl⟩ joint.weth9.unlocked rfl start.1 start.2
  obtain ⟨-, -, -, -, -, -, -, rep⟩ := replayed
  obtain ⟨-, -, -, slot6, -⟩ := rep.fixed
  obtain ⟨inst, admin⟩ := Usdc.usdc_history_end_installed trace
    (⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩ : Usdc.UsdcHist usdc KU trace)
  refine ⟨?_, by rw [state]; exact inst, by rw [state]; exact admin⟩
  have storPair : pre.getStor pair = future.state.getStor pair :=
    congrArg (fun w : Jaune.State => w.getStor pair) state
  rw [storPair, ← joint.token0]
  exact slot6.trans tokens.1

theorem syncFirstWorld_getCode (sevm : Sevm) (pre : Devm) (a : Adr) :
    (syncFirstWorld sevm pre).getCode a = pre.getCode a := by
  unfold syncFirstWorld syncLockedWorld
  rw [afterSload_getCode, afterSstore_getCode, afterSload_getCode]

theorem notPrecompile_usdc {pair usdc weth : Adr} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State} {sevm : Sevm}
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ w) (fork : CoveredFork sevm.benvStat.fork) :
    sevm.benvStat.rules.isPrecomp usdc = (false = true) := by
  rw [Bool.false_eq_true]
  exact eq_false (joint.usdcNotPrecompile _ fork)

/-- **C6(c), the sync liveness row with both tokens' queries discharged** (USDC = token0, WETH9 =
token1).  As `pair_history_sync_live`, from the two-token joint checkpoint: WETH9's second query is
pinned (`_read1`) to `syncWethRead1` over USDC's gas-free skeleton, and USDC's first query is pinned
(`_read0`) to `syncUsdcRead0` at the call gas WETH9's pin fixes.  What stays is the Pair's own sentry,
the frame's call depth (two levels, for USDC's delegatecall), the Pair not USDC's admin word, and the
legs' gas sentries.  No never-signer premise: the route needs no holder law. -/
theorem pair_usdc_weth9_history_sync_live {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (_read1 : (d1, callGas1) = syncWethRead1 sevm (syncUsdcRead0Skel sevm pre) G)
    (_read0 : (d0, callGas0) = syncUsdcRead0 sevm pre callGas1)
    (fits0 : callGas0 < 2 ^ 256) (fits1 : callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (syncUsdcRead0Skel sevm pre) +
        usdcBalUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
          (syncFirstToken sevm pre)))
    (room1 : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    SyncLiveOutcome pair trace KP st₀ sevm pre d0 d1 callGas0 G := by
  exact pair_usdc_weth9_history_sync_live_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size selector static depth notAdmin sentry _read1 _read0 fits0 fits1 room0 room1

end Blanc.Composition.UniswapV2PairUsdcWeth9
