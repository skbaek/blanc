import Blanc.Lift.UniswapV2Pair.MintPositionalRoot
import Blanc.Lift.UniswapV2Pair.PairFeeReturn

/-! Mint's fee, pricing, and public suffixes share the actual call certificate. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem mintReturnEntries_noHalt : NoHaltSet cert.prog mintFinalExecFreeEntries = true := by decide

/-- The actual fee reply, fee return, Mint return and public halt share one root.
The source suffixes start at those very original continuation nodes. -/
theorem MintRootCallPositions.suffixes {root : Exec.Deriv} {b post : Devm}
    (r : MintRootCallPositions root b) (success : root.exn = .ok post)
    (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ (feeN mintN : Exec.Deriv) (feeCursor mintCursor : Cursor) (feeGas : Nat),
      Exec.Deriv.ExecFreeUntil r.fee.occurrence.call.returned feeN ∧
      feeN.sevm = root.sevm ∧ feeN.exn = .ok post ∧
      CursorOK code cert feeN feeCursor ∧ feeCursor.f = t_1233_c41 ∧
      feeCursor.K.map Cont.f = [t_039b_c86] ∧
      feeBranchAccepts root.sevm
        (feeKLastWorld root.sevm r.fee.occurrence.call.returned.devm)
        (feeKLastWord root.sevm r.fee.occurrence.call.returned.devm)
        (Bytes.toB256 (r.fee.out.take 32)) (mintRootReserve0 root b) (mintRootReserve1 root b) ∧
      feeN.devm = feeBranchPost root.sevm
        (feeKLastWorld root.sevm r.fee.occurrence.call.returned.devm)
        (mintFeeLocals (Bytes.toB256 (r.out1.take 32) - mintRootReserve1 root b)
          (Bytes.toB256 (r.out0.take 32) - mintRootReserve0 root b)
          (Bytes.toB256 (r.out1.take 32)) (Bytes.toB256 (r.out0.take 32))
          (mintRootReserve1 root b) (mintRootReserve0 root b)
          (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842])
        (feeReplyMemory (balanceReplyMemory
          (balanceReplyMemory getterInitMemory root.sevm.currentTarget r.out0)
          r.first.call.returned.sevm.currentTarget r.out1) r.fee.out)
        (feeKLastWord root.sevm r.fee.occurrence.call.returned.devm)
        (Bytes.toB256 (r.fee.out.take 32)) (mintRootReserve0 root b) (mintRootReserve1 root b) feeGas ∧
      Exec.Deriv.ExecFreeUntil feeN mintN ∧
      mintN.sevm = root.sevm ∧ mintN.exn = .ok post ∧
      CursorOK code cert mintN mintCursor ∧ mintCursor.f = t_039b_c86 ∧
      mintCursor.K.map Cont.f = [] ∧
      SFunc.Run cert.prog root.sevm feeN.devm t_1233_c41 (.returned mintN.devm) ∧
      SFunc.Run cert.prog root.sevm mintN.devm t_039b_c86 (.halted post) := by
  have env0 := r.first.returned_sevm
  have env1 := r.second.returned_sevm.trans env0
  have outcome0 := r.first.returned_exn.trans success
  have outcome1 := r.second.returned_exn.trans outcome0
  have mem0 := balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget
  have mem1 := balanceReplyMemory_ptr r.out0 mem0
  have mem2 := balanceRequestMemory_ptr mem1 r.first.call.returned.sevm.currentTarget
  have mem3 := balanceReplyMemory_ptr r.out1 mem2
  have low (word : B256) : (word &&& reserveMask112).toNat < 2 ^ 112 := by
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat word (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨feeN, feeCursor, spanFee, envFee, outcomeFee, placedFee, treeFee, contsFee,
      guards, feeGas, stateFee⟩ := r.fee.returnState outcome1
    (by rw [env1]; exact fork) mem3 (low _) (low _)
  have actualFeeEnv := envFee.trans env1
  obtain ⟨mintN, mintCursor, spanMint, envMint, outcomeMint, placedMint, treeMint,
      contsMint, sourceMint⟩ := placedFee.quietReturn cert_check outcomeFee
    (by rw [actualFeeEnv]; exact fork) mintFinalExecFreeEntries_closed mintReturnEntries_noHalt
    (by rw [treeFee]; decide) (by rw [treeFee]; decide) contsFee
  have actualMintEnv := envMint.trans actualFeeEnv
  have actualMintOutcome := outcomeMint.trans outcomeFee
  obtain halted | returned := placedMint.sourceRunReturn cert_check actualMintOutcome
    (by rw [actualMintEnv]; exact fork)
  · rw [treeMint, actualMintEnv] at halted
    rw [treeFee, actualFeeEnv] at sourceMint
    refine ⟨feeN, mintN, feeCursor, mintCursor, feeGas,
      spanFee, actualFeeEnv, outcomeFee, placedFee, treeFee, contsFee, ?_, ?_,
      spanMint, actualMintEnv, actualMintOutcome, placedMint, treeMint, contsMint,
      sourceMint, halted.mono StepIn.toRun⟩
    · simpa only [env1] using guards
    · simpa only [env1] using stateFee
  · obtain ⟨k, K, state, run, sameK, _, _, _, _⟩ := returned
    have empty : mintCursor.K = [] := List.map_eq_nil_iff.mp contsMint
    rw [empty] at sameK
    cases sameK

end Blanc.Lift.UniswapV2Pair
