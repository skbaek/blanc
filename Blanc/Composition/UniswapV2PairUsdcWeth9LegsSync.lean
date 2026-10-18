import Blanc.Composition.UniswapV2PairUsdcWeth9LegsRead
import Blanc.Composition.UniswapV2PairWeth9LegsSync

/-!
# sync's USDC `balanceOf` query (U9c)

The read-side keeps fact for USDC's `balanceOf` STATICCALL (`usdcBalanceCall_state`,
`usdcBalanceSkel_state`: the query, and its gas-free skeleton, leave the world as it was), the read
leg at the fixed pointer `128` (`usdcReadLeg128_spec`, shared with mint), and sync's first query with
USDC as `token0` (`syncUsdcRead0`, its skeleton and spec).
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairWeth9Joint

/-- USDC's `balanceOf` proxy frame leaves the world as it was. -/
theorem proxyBalPost_state (s : Sevm) (pre : Devm) (X : Nat) :
    (proxyBalPost s pre X).state = pre.state := by
  unfold proxyBalPost
  rw [proxyPost_state]
  unfold balChild implBalPost
  rw [Devm.withOutput_state, Devm.memRead_state, St_state, Blanc.Lift.NodeWalk.afterSload_state]
  show (dParent s pre 0).state = _
  rw [callSpawnParent_state, addAccessedAddress_state]
  exact UsdcToken.pBase_state s pre

section Keeps

theorem callChildPost_state' (P c : Devm) (oi os : Nat) : (callChildPost P c oi os).state = c.state :=
  rfl

theorem withGasLeft_state' (d : Devm) (x : Nat) : (d.withGasLeft x).state = d.state := rfl

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)

theorem bChildB_state : (bChildB sevm B S M p t).state = B.state := by
  show (balParent sevm B S M p t 0 0).state = _
  unfold balParent balWarm balPopped
  rw [callSpawnParent_state, addAccessedAddress_setMach_state, Lift.temporalAccountAccessBase_state]

/-- **The read-side keeps fact, skeleton form**: USDC's `balanceOf` query leaves the world (every
account's storage, code and balance) as it was. -/
theorem usdcBalanceSkel_state : (usdcBalanceSkel sevm B S M p t).state = B.state := by
  unfold usdcBalanceSkel
  rw [callChildPost_state', proxyBalPost_state, bChildB_state]

/-- **The read-side keeps fact**: USDC's `balanceOf` STATICCALL at any call gas leaves the world
(every account's storage, code and balance) as it was. -/
theorem usdcBalanceCall_state (cg : Nat) : (usdcBalanceCall sevm B S M p t cg).state = B.state := by
  unfold usdcBalanceCall
  rw [usdcBalanceCallAt_eq, withGasLeft_state']
  exact usdcBalanceSkel_state sevm B S M p t

end Keeps

/-- **The USDC read leg at pointer `128`** (the sync and mint request layout): the record data of one
USDC `balanceOf(pair)` query staged by the Pair's `balanceRequestMemory` at a masked token word, and
its result as the skeleton up to gas. -/
theorem usdcReadLeg128_spec {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {t : B256}
    {need : Devm → Nat} (ht : swapTokenWord t = t) (gasFree : ∀ d x, need (d.withGasLeft x) = need d)
    (fork : CoveredFork sevm.benvStat.fork) (inst : UsdcInstalled t.toAdr B.state)
    (depth : 2 ≤ sevm.depth) (notPrecompile : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (notAdmin : sevm.currentTarget ≠ adminOf B.state t.toAdr)
    (stackRoom : S.length < 1018) (wf : Mem.Wf M)
    (fits : (usdcReadLeg sevm B S M 128 t need).2 < 2 ^ 256)
    (room : usdcBalNeed sevm B S M 128 t ≤
      except64th (need (usdcBalanceSkel sevm B S M 128 t) + usdcBalUsed sevm B S M 128 t)) :
    (B.getCode t.toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase B t.toAdr)
        ((usdcReadLeg sevm B S M 128 t need).2.toB256 :: t :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: t :: S)
        (balanceRequestMemory M sevm.currentTarget) (usdcReadLeg sevm B S M 128 t need).2)
      (.exec .staticcall) (usdcReadLeg sevm B S M 128 t need).1 ∧
    (usdcReadLeg sevm B S M 128 t need).1.stack = 1 :: 164 :: 0x70a08231 :: t :: S ∧
    (usdcReadLeg sevm B S M 128 t need).1.gasLeft = need (usdcReadLeg sevm B S M 128 t need).1 ∧
    32 ≤ (usdcReadLeg sevm B S M 128 t need).1.returnData.length ∧
    (usdcReadLeg sevm B S M 128 t need).1.returnData =
      (Nat.toB256 (balanceBits ((B.state.getStor t.toAdr).get (balSlot sevm.currentTarget)))).toBytes ∧
    (usdcReadLeg sevm B S M 128 t need).1 =
      (usdcBalanceSkel sevm B S M 128 t).withGasLeft (usdcReadLeg sevm B S M 128 t need).1.gasLeft := by
  have htok : balTok t = t.toAdr := by unfold balTok; rw [ht]
  obtain ⟨hrun, hstk, hret, hgas⟩ := usdcReadLeg_spec (sevm := sevm) (B := B) (S := S) (M := M)
    (p := 128) (t := t) (need := need) gasFree fork (by rw [htok]; exact inst) depth
    (by rw [htok]; exact notPrecompile) (by rw [htok]; exact notAdmin) stackRoom wf (by decide) fits
    room
  rw [balCallState_128 _ ht] at hrun
  rw [htok] at hret
  have hcode : (B.getCode t.toAdr).size.toB256 ≠ 0 := by
    have hc : B.state.getCode t.toAdr = Proxy.code := code_of_at (d := B) inst.proxy
    change (B.state.getCode t.toAdr).size.toB256 ≠ 0
    rw [hc]
    exact proxy_code_size_word
  refine ⟨hcode, hrun, ?_, hgas, by rw [hret, B256.length_toBytes], hret, ?_⟩
  · rw [hstk]
    unfold balRest
    rw [ht]
    rfl
  · show usdcBalanceCall sevm B S M 128 t (usdcReadLegGas sevm B S M 128 t need) =
      (usdcBalanceSkel sevm B S M 128 t).withGasLeft
        (usdcBalanceCall sevm B S M 128 t (usdcReadLegGas sevm B S M 128 t need)).gasLeft
    unfold usdcBalanceCall
    rw [usdcBalanceCallAt_eq]
    rfl

end Blanc.Composition.UsdcLive

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcLive

/-- **sync's first `balanceOf(pair)` query with USDC as `token0`**: its result and the call gas
USDC's code determines, given the second query's call gas `callGas1`.  Reuses U9a's `usdcReadLeg`
over the predecessor's staging (`syncFirstWorld`, `syncTail`, `syncRead0Need`). -/
noncomputable def syncUsdcRead0 (sevm : Sevm) (pre : Devm) (callGas1 : Nat) : Devm × Nat :=
  usdcReadLeg sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128 (syncFirstToken sevm pre)
    (syncRead0Need sevm callGas1)

/-- The gas-free skeleton of sync's USDC query result (what WETH9's second query reads). -/
noncomputable def syncUsdcRead0Skel (sevm : Sevm) (pre : Devm) : Devm :=
  usdcBalanceSkel sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128 (syncFirstToken sevm pre)

/-- **sync's USDC first-query leg (USDC = token0), frame level.**  USDC installed at the token the
lock prefix loads, not a precompile, two levels of call depth, the Pair not the admin word, the call
gas a word, room for USDC's view under the 63/64 rule: `syncUsdcRead0` meets
`pair_history_sync_live`'s `nonzero0`, `call0`, `success0`, `returnedGas0` and `long0`, the reply is
the Pair's USDC balance bits, and the result is the skeleton up to gas. -/
theorem syncUsdcRead0_spec {sevm : Sevm} {pre : Devm} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : 2 ≤ sevm.depth)
    (inst : Usdc.UsdcInstalled (syncFirstToken sevm pre).toAdr (syncFirstWorld sevm pre).state)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (syncFirstToken sevm pre).toAdr = false)
    (notAdmin : sevm.currentTarget ≠ Usdc.adminOf (syncFirstWorld sevm pre).state
      (syncFirstToken sevm pre).toAdr)
    (fits : (syncUsdcRead0 sevm pre callGas1).2 < 2 ^ 256)
    (room : usdcBalNeed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (syncUsdcRead0Skel sevm pre) +
        usdcBalUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
          (syncFirstToken sevm pre))) :
    let d0 := (syncUsdcRead0 sevm pre callGas1).1
    let callGas0 := (syncUsdcRead0 sevm pre callGas1).2
    ((syncFirstWorld sevm pre).getCode (syncFirstToken sevm pre).toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm pre) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0 ∧
    d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 ::
      [0xfff6cae9] ∧
    d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70 ∧
    32 ≤ d0.returnData.length ∧
    d0.returnData = (Nat.toB256 (Usdc.balanceBits (((syncFirstWorld sevm pre).state.getStor
      (syncFirstToken sevm pre).toAdr).get (Usdc.balSlot sevm.currentTarget)))).toBytes ∧
    d0 = (syncUsdcRead0Skel sevm pre).withGasLeft d0.gasLeft :=
  usdcReadLeg128_spec (swapTokenWord_adr _) (syncRead0Need_gasFree sevm callGas1) fork inst depth
    notPrecompile notAdmin (by decide) getterInitMemory_ptr.wf fits room

end Blanc.Composition.UniswapV2PairUsdcWeth9

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

theorem temporalAccountAccessBase_setMach (B : Devm) (a : Adr) (m : Mach) :
    temporalAccountAccessBase (B.setMach m) a = (temporalAccountAccessBase B a).setMach m := by
  unfold temporalAccountAccessBase
  rw [show (B.setMach m).accessedAddresses = B.accessedAddresses from rfl]
  split <;> rfl

/-- **WETH9's read leg reads its base world's state, not its machine** (beyond the state-gas
meter). -/
theorem wethReadLeg_setMach (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256)
    (need : Devm → Nat) (m : Mach) (hm : m.stateGas = B.mach.stateGas) :
    wethReadLeg sevm (B.setMach m) S M p t need = wethReadLeg sevm B S M p t need := by
  have hT := temporalAccountAccessBase_setMach B (balTok t) m
  have hP : ∀ g, balPopped sevm (B.setMach m) S M p t g = balPopped sevm B S M p t g := by
    intro g; unfold balPopped; rw [hT, Devm.setMach_setMach]; congr 2
    show m.stateGas = _
    rw [hm]; unfold temporalAccountAccessBase; split <;> rfl
  have hW : ∀ g, balWarm sevm (B.setMach m) S M p t g = balWarm sevm B S M p t g := by
    intro g; unfold balWarm; rw [hP]
  have hE : balExt sevm (B.setMach m) S M p t = balExt sevm B S M p t := by
    unfold balExt; rw [hP]
  have hA : balAcc (B.setMach m) t = balAcc B t := by
    unfold balAcc; rw [hT]; rfl
  have hS : ∀ cg, balSplit sevm (B.setMach m) S M p t cg = balSplit sevm B S M p t cg := by
    intro cg; unfold balSplit; rw [hE, hA]
  have hPar : ∀ g k, balParent sevm (B.setMach m) S M p t g k = balParent sevm B S M p t g k := by
    intro g k; unfold balParent; rw [hW]
  have hM : ∀ g k f, balMsg sevm (B.setMach m) S M p t g k f = balMsg sevm B S M p t g k f := by
    intro g k f; unfold balMsg; rw [hPar]; rfl
  have hU : balUsed sevm (B.setMach m) S M p t = balUsed sevm B S M p t := by
    unfold balUsed; rw [hM]
  have hSk : wethBalanceSkel sevm (B.setMach m) S M p t = wethBalanceSkel sevm B S M p t := by
    unfold wethBalanceSkel; rw [hPar, hM]
  have hC : ∀ cg, wethBalanceCall sevm (B.setMach m) S M p t cg =
      wethBalanceCall sevm B S M p t cg := by
    intro cg; unfold wethBalanceCall wethBalanceCallAt; rw [hS, hE, hU, hPar, hM]
  unfold wethReadLeg readLegGas
  rw [hSk, hA, hE, hU, hC]

/-- **sync's WETH9 second query reads its first query's result up to gas.** -/
theorem syncWethRead1_withGasLeft (sevm : Sevm) (d : Devm) (G x : Nat) :
    syncWethRead1 sevm (d.withGasLeft x) G = syncWethRead1 sevm d G := by
  unfold syncWethRead1 Devm.withGasLeft
  rw [afterSload_setMach, wethReadLeg_setMach sevm (afterSload sevm d 7) _ _ _ _ _
    { d.mach with gasLeft := x } (afterSload_stateGas (sevm := sevm) (base := d) (key := 7)).symm]
  rfl

end Blanc.Composition.UniswapV2PairWeth9Joint
