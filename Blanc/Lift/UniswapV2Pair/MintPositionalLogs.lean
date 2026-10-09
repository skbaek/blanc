import Blanc.Lift.UniswapV2Pair.MintPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The three particular static replies preserve the original raw log prefix. -/
theorem MintRootCallPositions.fee_base_logs {root : Exec.Deriv} {b : Devm}
    (r : MintRootCallPositions root b) : (mintPositionalFeeBase r).logs = b.logs := by
  rw [mintPositionalFeeBase, feeKLastWorld, afterSload_logs, r.fee.reply.logs,
    feeFactoryCallWorld, temporalAccountAccessBase_logs, feeFactoryLoadWorld,
    afterSload_logs, r.post1.logs, mintRootSecondWorld, temporalAccountAccessBase_logs,
    afterSload_logs, r.post0.logs, mintRootFirstWorld, temporalAccountAccessBase_logs,
    afterSload_logs, mintRootReserves, afterSload_logs, mintLockedWorld,
    afterSstore_logs, afterSload_logs]

/-- The canonical fee state and source fee events have the same original raw prefix. -/
theorem MintPositionalCanonicalResult.fee_logs {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : MintPositionalCanonicalResult K current invocation root b post) :
    ∃ feeLogs : List Log, r.feeNode.devm.logs = b.logs ++ feeLogs ∧
      (((mintPositionalFeeResult current r.positions).events = [] ∧ feeLogs = []) ∨
        ∃ L : B256, L ≠ 0 ∧
          (mintPositionalFeeResult current r.positions).events =
            [.transfer 0 (mintPositionalFeeWord r.positions).toAdr L] ∧
          feeLogs = [lpMintRawLog root.sevm.currentTarget
            (mintPositionalFeeWord r.positions).toAdr L]) := by
  have shape := r.sourceFee.2.2.2.2
  rw [← r.feeState] at shape
  rcases shape with ⟨events, logs⟩ | ⟨L, nonzero, events, logs⟩
  · exact ⟨[], by rw [logs, r.positions.fee_base_logs, List.append_nil], Or.inl ⟨events, rfl⟩⟩
  · exact ⟨_, by rw [logs, r.positions.fee_base_logs], Or.inr ⟨L, nonzero, events, rfl⟩⟩

/-- The same canonical source result appends precisely the raw events of the
original run, including the fee mint and the first-mint minimum when present. -/
theorem MintPositionalCanonicalResult.log_image {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : MintPositionalCanonicalResult K current invocation root b post)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state) :
    ∃ (added : List PendingLog) (raw : List Log),
      r.final.current.logs = current.logs ++ added ∧
      post.logs = b.logs ++ raw ∧
      added.map (PendingLog.rawWith (mintOwnedRaw root.sevm.currentTarget)) = raw.map some := by
  obtain ⟨cache0, cache1, _, _, _⟩ := r.positions.cache_targets rep
  obtain ⟨feeLogs, feeRaw, feeShape⟩ := r.fee_logs
  have raw := r.logs
  rw [feeRaw, cache0, cache1] at raw
  obtain ⟨liquidity, bytes, sourceLogs⟩ := mintAfterFee_finished_logs r.typedFinished
  have word : liquidity.toB256 = r.liquidity.toB256 := by
    have words := congrArg Bytes.toB256 bytes.symm
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      B256.toB256_toBytes] using words
  rw [word] at sourceLogs
  refine ⟨_, _, sourceLogs, ?_, mint_logs_raw feeShape⟩
  rw [raw]
  simp only [List.append_assoc]
  rfl

end Blanc.Lift.UniswapV2Pair
