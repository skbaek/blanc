import Blanc.Lift.UniswapV2Pair.SyncCanonical
import Blanc.Lift.UniswapV2Pair.Jumps

/-! Canonical Sync gas consumer of the accepted exact constructor. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual update/unlock schedule; no caller-selected primitive charges. -/
def syncUpdateUnlockClosedGas (sevm : Sevm) (b : Devm)
    (balance0 balance1 : B256) (n G : Nat) : Nat :=
  let u := afterSload sevm b 8
  let old0 := reserve0Read (b.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (b.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  syncUpdateUnlockGas sevm b balance0 balance1 n
    (sloadCost sevm u 8)
    (sloadCost sevm h 9)
    (sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (sloadCost sevm w9 10)
    (sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (sloadCost sevm v 8)
    (sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1)) G

/-- Exact liveness with the same actual canonical returned worlds and views. -/
theorem syncPc0_canonical_live {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b d0 d1 : Devm}
    {callGas0 callGas1 G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code)
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
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1 (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length)
    (bound0 : (Bytes.toB256 (d0.returnData.take 32)).toNat < 2 ^ 112)
    (bound1 : (Bytes.toB256 (d1.returnData.take 32)).toNat < 2 ^ 112) :
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
      (run : Exec 0 sevm
        (St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229)) (.ok post)),
      post.gasLeft = G ∧
      ∀ (hashTInj : WriterInj (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩)))
        (hashTApart : WriterApart (WriterExtend K (syncTraceKeys
          ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
            .ok post, run⟩))),
        ∃ result : SyncCanonicalResult K current invocation
            ⟨0, sevm, St b [] Mem.empty (syncCalleePrefixGas sevm b callGas0 + 15 + 229),
              .ok post, run⟩ b post,
          result.returned0.devm = d0 ∧ result.returned1.devm = d1 ∧
          result.out0 = d0.returnData ∧ result.out1 = d1.returnData := by
  dsimp only
  intro sentry8 sentry10 sentry9 unlockSentry
  let balance0 := Bytes.toB256 (d0.returnData.take 32)
  let balance1 := Bytes.toB256 (d1.returnData.take 32)
  let u := afterSload sevm d1 8
  let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
  let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
  let h := afterSload sevm u 8
  let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
  let v := updateOracleWorld sevm u old0 old1
  have exactRun := syncPc0_exact
    (headerLoad := sloadCost sevm u 8)
    (load9 := sloadCost sevm h 9)
    (store9 := sstoreCost sevm (afterSload sevm h 9) 9
      (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
        (updatePriceWord old0 old1) delta))
    (load10 := sloadCost sevm w9 10)
    (store10 := sstoreCost sevm (afterSload sevm w9 10) 10
      (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
        (updatePriceWord old1 old0) delta))
    (load8 := sloadCost sevm v 8)
    (store8 := sstoreCost sevm (afterSload sevm v 8) 8
      (updateFinalPackedWord sevm u old0 old1 balance0 balance1))
    fork value size selector static unlocked sentry nonzero0 call0 success0 returnedGas0 long0
    nonzero1 call1 success1
    (by simpa only [syncUpdateUnlockClosedGas] using returnedGas1)
    long1 bound0 bound1 rfl rfl rfl (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
    sentry8 sentry10 sentry9 unlockSentry
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork exactRun
  refine ⟨_, run, rfl, ?_⟩
  intro hashTInj hashTApart
  obtain ⟨result⟩ := sync_canonical_source_frame_result invocation rep sem image installed
    codeEq fork selector run hashTInj hashTApart
  obtain ⟨firstFree, firstPc, firstSevm, firstInst, firstEdge, firstResult,
    secondFree, secondPath, secondPc, secondSevm, secondOutcome, secondInst,
    secondEdge, secondResult, _⟩ := result.order
  have firstInput : result.first.node.devm =
      St (temporalAccountAccessBase (syncFirstWorld sevm b) (syncFirstToken sevm b).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm b) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm b) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0 := by
    refine ?_
  obtain ⟨slot0, filled0, step0⟩ := call0
  have actual0 := result.first.stepRun
  rw [firstInst, firstSevm, firstInput] at actual0
  have output0 : result.first.stepResult = .ok d0 :=
    (Blanc.Step.Run.unique_of_filled result.first.filled filled0 actual0
      (step0 result.first.node.pc)).2
  have returned0Eq : result.returned0.devm = d0 := Except.ok.inj (firstResult.symm.trans output0)
  have secondInput : result.second.node.devm =
      St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1 := by
    refine ?_
  obtain ⟨slot1, filled1, step1⟩ := call1
  have actual1 := result.second.stepRun
  rw [secondInst, secondSevm, secondInput] at actual1
  have output1 : result.second.stepResult = .ok d1 :=
    (Blanc.Step.Run.unique_of_filled result.second.filled filled1 actual1
      (step1 result.second.node.pc)).2
  have returned1Eq : result.returned1.devm = d1 := Except.ok.inj (secondResult.symm.trans output1)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data0, _⟩ := result.firstCall
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data1, _⟩ := result.secondCall
  refine ⟨result, returned0Eq, returned1Eq, ?_, ?_⟩
  · exact data0.symm.trans (congrArg Devm.returnData returned0Eq)
  · exact data1.symm.trans (congrArg Devm.returnData returned1Eq)

end Blanc.Lift.UniswapV2Pair
