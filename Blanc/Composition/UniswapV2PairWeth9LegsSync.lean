import Blanc.Composition.UniswapV2PairWeth9LegsSwap0Read
import Blanc.Lift.UniswapV2Pair.SyncGasCanonical

/-!
# The sync row's WETH9 `balanceOf` legs (C4(b), U8b1)

`pair_history_sync_live` takes the two token `balanceOf(pair)` `STATICCALL`s as premises
(`nonzero0`/`call0`/`success0`/`returnedGas0`/`long0` and the `…1` set).  For the WETH9 side,
either `token0` (`syncWethRead0`) or `token1` (`syncWethRead1`), the query is the generic read leg
(`wethReadLeg`) at the fixed pointer `128`, and its spec gives those premises verbatim.  Code-only:
WETH9's code at the token, no precompile, call depth, the call gas a word, room for the view.

The fixed-pointer bridge (`wethReadLeg128_spec`) is shared with the mint row's reads.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The read leg at the fixed pointer `128` -/

theorem swapBalanceReply_128 (M : Mem) (pair : Adr) (out : Bytes) :
    swapBalanceReply M 128 pair out = balanceReplyMemory M pair out := rfl

theorem balCallState_128 {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {t : B256} (cg : Nat)
    (ht : swapTokenWord t = t) :
    balCallState sevm B S M 128 t cg =
      St (temporalAccountAccessBase B t.toAdr)
        (cg.toB256 :: t :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t :: S)
        (balanceRequestMemory M sevm.currentTarget) cg := by
  unfold balCallState balRest balTok
  rw [ht]
  rfl

/-- **The read leg at pointer `128`** (the sync and mint request layout): the record data of one
WETH9 `balanceOf(pair)` query staged by the Pair's `balanceRequestMemory` at a masked token word. -/
theorem wethReadLeg128_spec {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {t : B256}
    {need : Devm → Nat} (ht : swapTokenWord t = t) (gasFree : ∀ d x, need (d.withGasLeft x) = need d)
    (fork : CoveredFork sevm.benvStat.fork)
    (hcode : B.state.getCode t.toAdr = Weth9.code) (depth : sevm.depth ≠ 0)
    (notPrecompile : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (stackRoom : S.length < 1018) (wf : Mem.Wf M)
    (fits : (wethReadLeg sevm B S M 128 t need).2 < 2 ^ 256)
    (room : balUsed sevm B S M 128 t ≤
      except64th (need (wethBalanceSkel sevm B S M 128 t) + balUsed sevm B S M 128 t)) :
    (B.getCode t.toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase B t.toAdr)
        ((wethReadLeg sevm B S M 128 t need).2.toB256 :: t :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: t :: S)
        (balanceRequestMemory M sevm.currentTarget) (wethReadLeg sevm B S M 128 t need).2)
      (.exec .staticcall) (wethReadLeg sevm B S M 128 t need).1 ∧
    (wethReadLeg sevm B S M 128 t need).1.stack = 1 :: 164 :: 0x70a08231 :: t :: S ∧
    (wethReadLeg sevm B S M 128 t need).1.gasLeft = need (wethReadLeg sevm B S M 128 t need).1 ∧
    32 ≤ (wethReadLeg sevm B S M 128 t need).1.returnData.length ∧
    (wethReadLeg sevm B S M 128 t need).1.returnData =
      (B.getStorVal t.toAdr (Weth9.balSlot sevm.currentTarget)).toBytes := by
  have htok : balTok t = t.toAdr := by unfold balTok; rw [ht]
  obtain ⟨hrun, hstk, hret, hgas⟩ := wethReadLeg_spec (sevm := sevm) (B := B) (S := S) (M := M)
    (p := 128) (t := t) (need := need) gasFree fork (by rw [htok]; exact hcode) depth
    (by rw [htok]; exact notPrecompile) stackRoom wf (by decide) fits room
  rw [balCallState_128 _ ht] at hrun
  rw [htok] at hret
  refine ⟨weth9_code_nonzero hcode, hrun, ?_, hgas, by rw [hret]; exact toBytes_long _, hret⟩
  rw [hstk]
  unfold balRest
  rw [ht]
  rfl

/-! ## sync, WETH9 = token0: the first query -/

section Sync0

variable (sevm : Sevm) (pre : Devm) (callGas1 : Nat)

/-- The words under the sync queries' operands (the frame's return tags). -/
def syncTail : List B256 := 0x1fd4 :: 0x0257 :: [0xfff6cae9]

/-- What sync needs left after its first query: the slot-7 read, the second request's staging and
the second query's call gas (the row's `returnedGas0`). -/
def syncRead0Need (d0 : Devm) : Nat :=
  callGas1 + 5 + 22 +
    temporalAccountAccessCost (afterSload sevm d0 7)
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
    sloadCost sevm d0 7 + 113 + 70

end Sync0

/-- **sync's first `balanceOf(pair)` query when WETH9 is `token0`**: its result and the call gas
WETH9's code determines, given the second query's call gas `callGas1`. -/
noncomputable def syncWethRead0 (sevm : Sevm) (pre : Devm) (callGas1 : Nat) : Devm × Nat :=
  wethReadLeg sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128 (syncFirstToken sevm pre)
    (syncRead0Need sevm callGas1)

theorem syncRead0Need_gasFree (sevm : Sevm) (callGas1 : Nat) (d : Devm) (x : Nat) :
    syncRead0Need sevm callGas1 (d.withGasLeft x) = syncRead0Need sevm callGas1 d := by
  unfold syncRead0Need Devm.withGasLeft
  rw [afterSload_setMach]
  rfl

/-- **sync's WETH9 first-query leg (WETH9 = token0), frame level.**  WETH9's code at the token the
lock prefix loads (`syncFirstToken`) in the world after the prefix (`syncFirstWorld`), not a
precompile, call depth left, the call gas a word, and room for WETH9's view: `syncWethRead0` meets
`pair_history_sync_live`'s `nonzero0`, `call0`, `success0`, `returnedGas0` and `long0`, and replies
with the pair's WETH9 balance there. -/
theorem syncWethRead0_spec {sevm : Sevm} {pre : Devm} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (syncFirstWorld sevm pre).state.getCode (syncFirstToken sevm pre).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (syncFirstToken sevm pre).toAdr = false)
    (fits : (syncWethRead0 sevm pre callGas1).2 < 2 ^ 256)
    (room : balUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (wethBalanceSkel sevm (syncFirstWorld sevm pre) syncTail
          getterInitMemory 128 (syncFirstToken sevm pre)) +
        balUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128 (syncFirstToken sevm pre))) :
    let d0 := (syncWethRead0 sevm pre callGas1).1
    let callGas0 := (syncWethRead0 sevm pre callGas1).2
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
    d0.returnData = ((syncFirstWorld sevm pre).getStorVal (syncFirstToken sevm pre).toAdr
      (Weth9.balSlot sevm.currentTarget)).toBytes :=
  wethReadLeg128_spec (swapTokenWord_adr _) (syncRead0Need_gasFree sevm callGas1) fork wethCode depth
    notPrecompile (by decide) getterInitMemory_ptr.wf fits room

/-! ## sync, WETH9 = token1: the second query -/

section Sync1

variable (sevm : Sevm) (d0 : Devm) (G : Nat)

/-- The words under sync's second query's operands (the first reply word on the tags). -/
def syncTail1 : List B256 := Bytes.toB256 (d0.returnData.take 32) :: syncTail

/-- The token sync's second query calls (slot 7, as the Pair loads it). -/
def syncToken1 : B256 := (d0.getStorVal sevm.currentTarget 7).toAdr.toB256

/-- What sync needs left after its second query: the update and unlock schedule to the frame's
residual `G` (the row's `returnedGas1`). -/
def syncRead1Need (d1 : Devm) : Nat :=
  syncUpdateUnlockClosedGas sevm d1 (Bytes.toB256 (d0.returnData.take 32))
    (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1) + 70

end Sync1

/-- **sync's second `balanceOf(pair)` query when WETH9 is `token1`**, staged over the first query's
result `d0`: its result and the call gas WETH9's code determines, given the frame's residual `G`. -/
noncomputable def syncWethRead1 (sevm : Sevm) (d0 : Devm) (G : Nat) : Devm × Nat :=
  wethReadLeg sevm (afterSload sevm d0 7) (syncTail1 d0)
    (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0)
    (syncRead1Need sevm d0 G)

section SetMach

variable (sevm : Sevm) (b : Devm) (m : Mach)

theorem updateAccumulatorPost_setMach (key price elapsed : B256) :
    updateAccumulatorPost sevm (b.setMach m) key price elapsed =
      (updateAccumulatorPost sevm b key price elapsed).setMach m := by
  unfold updateAccumulatorPost
  rw [afterSload_setMach, Devm.getStorVal_setMach, afterSstore_setMach]

theorem updateOracleActive_setMach (old0 old1 : B256) :
    updateOracleActive sevm (b.setMach m) old0 old1 = updateOracleActive sevm b old0 old1 := rfl

theorem updateOracleWorld_setMach (old0 old1 : B256) :
    updateOracleWorld sevm (b.setMach m) old0 old1 = (updateOracleWorld sevm b old0 old1).setMach m := by
  unfold updateOracleWorld
  simp only [updateOracleActive_setMach, Devm.getStorVal_setMach, afterSload_setMach,
    updateAccumulatorPost_setMach, ite_setMach]

theorem updateFinalPackedWord_setMach (old0 old1 balance0 balance1 : B256) :
    updateFinalPackedWord sevm (b.setMach m) old0 old1 balance0 balance1 =
      updateFinalPackedWord sevm b old0 old1 balance0 balance1 := by
  unfold updateFinalPackedWord
  rw [updateOracleWorld_setMach, Devm.getStorVal_setMach]

theorem syncUpdatedWorld_setMach (balance0 balance1 : B256) :
    syncUpdatedWorld sevm (b.setMach m) balance0 balance1 =
      (syncUpdatedWorld sevm b balance0 balance1).setMach m := by
  unfold syncUpdatedWorld updateWorld updateSyncPost updatePackedPost
  rw [Devm.getStorVal_setMach, afterSload_setMach, updateOracleWorld_setMach,
    updateFinalPackedWord_setMach, afterSload_setMach, Devm.getStorVal_setMach, afterSstore_setMach,
    addLog_setMach]

theorem syncUpdateUnlockClosedGas_setMach (balance0 balance1 : B256) (n G : Nat) :
    syncUpdateUnlockClosedGas sevm (b.setMach m) balance0 balance1 n G =
      syncUpdateUnlockClosedGas sevm b balance0 balance1 n G := by
  unfold syncUpdateUnlockClosedGas syncUpdateUnlockGas
  simp only [afterSload_setMach, Devm.getStorVal_setMach, updateAccumulatorPost_setMach,
    updateOracleWorld_setMach, updateOracleActive_setMach, syncUpdatedWorld_setMach,
    updateFinalPackedWord_setMach, sstoreCost_setMach, sloadCost_setMach']

end SetMach

theorem syncRead1Need_gasFree (sevm : Sevm) (d0 : Devm) (G : Nat) (d : Devm) (x : Nat) :
    syncRead1Need sevm d0 G (d.withGasLeft x) = syncRead1Need sevm d0 G d := by
  unfold syncRead1Need Devm.withGasLeft
  rw [syncUpdateUnlockClosedGas_setMach]
  rfl

/-- **sync's WETH9 second-query leg (WETH9 = token1), frame level.**  Over the first query's result
`d0`: WETH9's code at the token sync loads from slot 7, not a precompile, call depth left, the call
gas a word, and room for WETH9's view: `syncWethRead1` meets `pair_history_sync_live`'s `nonzero1`,
`call1`, `success1`, `returnedGas1` and `long1`, and replies with the pair's WETH9 balance there.
Code-only: nothing is assumed of the first token's query beyond its result world. -/
theorem syncWethRead1_spec {sevm : Sevm} {d0 : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : (afterSload sevm d0 7).state.getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr = false)
    (fits : (syncWethRead1 sevm d0 G).2 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128 (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    let d1 := (syncWethRead1 sevm d0 G).1
    let callGas1 := (syncWethRead1 sevm d0 G).2
    ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0 ∧
    Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1 ∧
    d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9] ∧
    d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1
      (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70 ∧
    32 ≤ d1.returnData.length ∧
    d1.returnData = ((afterSload sevm d0 7).getStorVal
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr (Weth9.balSlot sevm.currentTarget)).toBytes :=
  wethReadLeg128_spec (swapTokenWord_adr _) (syncRead1Need_gasFree sevm d0 G) fork wethCode depth
    notPrecompile (by simp only [syncTail1, syncTail, List.length_cons, List.length_nil]; omega)
    (by rw [← swapBalanceReply_128]; exact swapBalanceReply_wf getterInitMemory_ptr.wf) fits room

end Blanc.Composition.UniswapV2PairWeth9Joint
