import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeSource
import Blanc.Lift.UniswapV2Pair.BurnLogImage

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnFourCallsH.prefixLogs {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCallsH root sevm b w)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget))
    (invocation : List Nat) (success : root.exn = .ok post) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) :
    ∃ (added : List PendingLog) (raw : List Log),
      (r.sourceTransferFrame current invocation).current.logs = current.logs ++ added ∧
      r.transfer.occurrence.node.devm.logs = b.logs ++ raw ∧
      added.map (PendingLog.rawWith (burnOwnedRaw sevm.currentTarget)) = raw.map some := by
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    ((Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans
      r.three.fee.occurrence.sevm_eq).trans
        ((Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm)
  have startEnv : r.three.initial.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm
  have sample : feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm = current.state.balanceOf sevm.currentTarget := by
    rw [startEnv]
    exact r.three.initial.sampled_liquidity incoming tracked
  obtain ⟨feeGas, pricingState, feeResult⟩ := r.fee_source_result incoming (by
    unfold BurnThreeCallsH.feeFresh at fresh
    rw [FeeMintFresh_kLastH]; exact fresh)
  have logsDisj := feeResult.2.2.2.2
  rw [← pricingState, feeBranchSourceFee_kLastH] at logsDisj
  have firstLogs : r.three.initial.first.returned.devm.logs = b.logs := by
    rw [r.three.initial.first_reply.logs, burnInitialWorld0H, accountAccessH_logs,
      burnTokensWorldH, afterSloadH_logs, afterSloadH_logs, burnInitialReserveWorldH,
      afterSloadH_logs, burnLockedWorldH, afterSstoreH_logs, afterSloadH_logs]
  have initialLogs : r.three.initial.second.returned.devm.logs = b.logs := by
    rw [r.three.initial.second_reply.logs, accountAccessH_logs, firstLogs]
  have baseLogs : (feeKLastWorldH r.three.initial.second.returned.sevm
      r.three.fee.occurrence.call.returned.devm).logs = b.logs := by
    rw [feeKLastWorldH, afterSloadH_logs, r.three.fee.reply.logs,
      r.three.worlds.2.1 _ _ startEnv, burnFeeCallWorldOfH, feeFactoryCallWorldH,
      accountAccessH_logs, feeFactoryLoadWorldH, afterSloadH_logs,
      feeBurnWorldH, afterSloadH_logs, initialLogs]
  let prior := burnPositionalAfterFeeFrame current invocation sevm
  let fee := r.three.sourceFee current
  have feeImage : ∃ feeLogs : List Log,
      r.pricing.devm.logs = b.logs ++ feeLogs ∧
      (fee.events.map (PendingLog.owned prior.origin)).map
        (PendingLog.rawWith (burnOwnedRaw sevm.currentTarget)) = feeLogs.map some := by
    rcases logsDisj with ⟨events, raw⟩ | ⟨L, _, events, raw⟩
    · refine ⟨[], by rw [raw, baseLogs, List.append_nil], ?_⟩
      rw [show fee.events = [] from events]
      rfl
    · refine ⟨[lpMintRawLog sevm.currentTarget (Bytes.toB256 (r.three.fee.out.take 32)).toAdr L],
        (by rw [baseLogs] at raw; simpa only [startEnv] using raw), ?_⟩
      rw [show fee.events = _ from events]
      simp only [List.map_cons, List.map_nil, PendingLog.rawWith, burnOwnedRaw,
        lockedOwnedRaw, transferRawLog, lpMintRawLog]
      rfl
  obtain ⟨feeLogs, pricingLogs, feeImage⟩ := feeImage
  let added := fee.events.map (PendingLog.owned prior.origin) ++
    [PendingLog.owned prior.origin (.transfer sevm.currentTarget 0 (current.state.balanceOf sevm.currentTarget))]
  let raw := feeLogs ++
    [lpBurnRawLog sevm.currentTarget sevm.currentTarget (current.state.balanceOf sevm.currentTarget)]
  have pending : (r.sourceTransferFrame current invocation).current.logs = current.logs ++ added := by
    simp only [BurnFourCallsH.sourceTransferFrame, burnPricedFrame, Frame.withEvents,
      BurnThreeCallsH.sourceObserved, burnPositionalAfterFeeFrame, burnPositionalFeeFrame,
      burnSourceLockedFrame, Frame.beginResume, Frame.origin, fee, prior, added,
      List.map_cons, List.map_nil, List.append_assoc]
    rfl
  have represented := r.pricingRep incoming fresh
  have lpFresh := r.pricingFresh incoming fresh tracked
  obtain ⟨_, _, _, _, _, _, _, _, lp⟩ := r.lp_source_result represented lpFresh success stateGas bal
  have rawPrefix : r.transfer.occurrence.node.devm.logs = b.logs ++ raw := by
    have lpLogs := lp.2.2.2.2.1
    change (r.three.transferWorld r.pricing r.residual).logs = _ at lpLogs
    rw [afterSloadH_logs, pricingLogs] at lpLogs
    simp only [env, toAdr_toB256, sample, List.append_assoc] at lpLogs
    have inputLogs : r.transfer.occurrence.node.devm.logs =
        (r.three.transferWorld r.pricing r.residual).logs :=
      (congrArg Devm.logs r.transfer_input).trans (Devm.setMach_logs _ _)
    exact inputLogs.trans lpLogs
  have prefixImage : added.map (PendingLog.rawWith (burnOwnedRaw sevm.currentTarget)) = raw.map some := by
    simp only [added, raw, List.map_append, feeImage, List.map_cons, List.map_nil,
      PendingLog.rawWith, burnOwnedRaw, lockedOwnedRaw, transferRawLog, lpBurnRawLog]
    rfl
  exact ⟨added, raw, pending, rawPrefix, prefixImage⟩

/-- The actual fee and LP-burn prefix has the same pending/raw log image as
the exact source frame suspended at the first retained transfer slot. -/
theorem BurnFourCalls.prefixLogs {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget))
    (invocation : List Nat) (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ (added : List PendingLog) (raw : List Log),
      (r.sourceTransferFrame current invocation).current.logs = current.logs ++ added ∧
      r.transfer.occurrence.node.devm.logs = b.logs ++ raw ∧
      added.map (PendingLog.rawWith (burnOwnedRaw sevm.currentTarget)) = raw.map some :=
  BurnFourCallsH.prefixLogs (r.toH fork) incoming fresh tracked invocation success fork.rules_stateGas_none fork.rules_bal_none


end Blanc.Lift.UniswapV2Pair
