import Blanc.Composition.UniswapV2PairUsdcWeth9LegsSync
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Composition.UniswapV2PairWeth9SyncLive
import Blanc.Lift.Usdc.HistFFacts

/-!
# C6(c): the sync liveness row over the support-free checkpoint (finite twin)

Twin of `UniswapV2PairUsdcWeth9SyncLive.lean`: `pair_usdc_frameF` is `pair_usdc_frame`
with `joint : JointCheckpoint2F …` and `usdc_history_end_installedF` in place of the
support version; `pair_usdc_weth9_history_sync_live_finite` is the sync row with the same
statement except the joint type. No quiet premise: the proof never uses USDC's joint
relation (no never-signer premise), only the history-end installed/admin facts and the
WETH9 side. The support-free world/code helpers (`usdc_world_congr`,
`syncFirstWorld_getCode`) live here under their original names and are shared with the
original row file; only the genuinely support-dependent helpers have `F` twins.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.Weth9Token Blanc.Composition.UsdcLive

/-- USDC's installed runtimes and admin word read only the world's codes and USDC's storage.
(Moved here from `UniswapV2PairUsdcWeth9SyncLive`: support-free, shared under its original
name.) -/
theorem usdc_world_congr {P : Adr} {w w' : Jaune.State} (code : ∀ a, w'.getCode a = w.getCode a)
    (stor : w'.getStor P = w.getStor P) :
    (Usdc.UsdcInstalled P w → Usdc.UsdcInstalled P w') ∧ Usdc.adminOf w' P = Usdc.adminOf w P := by
  refine ⟨fun inst => ⟨?_, ?_, ?_, ?_, inst.implApart, inst.libApart⟩, ?_⟩
  · rw [code]; exact inst.proxy
  · rw [code]; exact inst.impl
  · rw [code]; exact inst.lib
  · rw [stor]; exact inst.slot
  · unfold Usdc.adminOf; rw [stor]

/-- **What a new Pair frame at the history's future world knows about USDC**, support-free
(twin of `pair_usdc_frame`). -/
theorem pair_usdc_frameF {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
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
  obtain ⟨inst, admin⟩ := Usdc.usdc_history_end_installedF trace
    (⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩ : Usdc.UsdcHistF usdc KU trace)
  refine ⟨?_, by rw [state]; exact inst, by rw [state]; exact admin⟩
  have storPair : pre.getStor pair = future.state.getStor pair :=
    congrArg (fun w : Jaune.State => w.getStor pair) state
  rw [storPair, ← joint.token0]
  exact slot6.trans tokens.1

theorem syncFirstWorld_getCode (sevm : Sevm) (pre : Devm) (a : Adr) :
    (syncFirstWorld sevm pre).getCode a = pre.getCode a := by
  unfold syncFirstWorld syncLockedWorld
  rw [afterSload_getCode, afterSstore_getCode, afterSload_getCode]

theorem notPrecompile_usdcF {pair usdc weth : Adr} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State} {sevm : Sevm}
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ w) (fork : CoveredFork sevm.benvStat.fork) :
    sevm.benvStat.rules.isPrecomp usdc = (false = true) := by
  rw [Bool.false_eq_true]
  exact eq_false (joint.usdcNotPrecompile _ fork)

/-- **C6(c), the sync liveness row, support-free** (USDC = token0, WETH9 = token1).
Twin of `pair_usdc_weth9_history_sync_live` with `joint : JointCheckpoint2F …` and no
quiet premise: the proof never uses USDC's joint relation. -/
theorem pair_usdc_weth9_history_sync_live_finite {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
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
  have h0 : (syncUsdcRead0 sevm pre callGas1).1 = d0 := (congrArg Prod.fst _read0).symm
  have hg : (syncUsdcRead0 sevm pre callGas1).2 = callGas0 := (congrArg Prod.snd _read0).symm
  obtain ⟨token0, inst, -⟩ := pair_usdc_frameF trace joint pairFresh usdcFresh wethFresh governance
    factoryInstalled factoryNotSystem state
  have tok : (syncFirstToken sevm pre).toAdr = usdc := by
    unfold syncFirstToken
    rw [toAdr_toB256, syncLockedWorld_slot (by decide), target]
    exact token0
  have keeps := syncFirstWorld_keeps sevm pre (w := usdc) (target ▸ joint.apart)
  obtain ⟨winst, wadmin⟩ := usdc_world_congr (P := usdc) (w := pre.state)
    (w' := (syncFirstWorld sevm pre).state) (syncFirstWorld_getCode sevm pre) keeps.2
  have spec := syncUsdcRead0_spec (callGas1 := callGas1) fork depth (by rw [tok]; exact winst inst)
    (by rw [tok]; exact notPrecompile_usdcF joint fork)
    (by rw [tok, wadmin, target]; exact notAdmin) (by rw [hg]; exact fits0) room0
  dsimp only at spec
  rw [h0, hg] at spec
  obtain ⟨nonzero0, call0, success0, returnedGas0, long0, -, skel⟩ := spec
  have read1 : (d1, callGas1) = syncWethRead1 sevm d0 G := by
    rw [_read1, skel, syncWethRead1_withGasLeft]
  exact pair_weth9_history_sync_live_one trace joint.weth9 pairFresh wethFresh factoryInstalled
    factoryNotSystem target state codeEq fork output representable value size selector static
    (by omega) sentry nonzero0 call0 success0 returnedGas0 long0 read1 fits1 room1

end Blanc.Composition.UniswapV2PairUsdcWeth9
