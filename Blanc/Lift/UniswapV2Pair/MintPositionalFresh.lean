import Blanc.Lift.UniswapV2Pair.MintPositionalFinish
import Blanc.Lift.UniswapV2Pair.MintCanonical
import Blanc.Lift.CursorOccurrenceRoots

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The fee recipient row comes from this original occurrence's retained reply. -/
theorem MintRootCallPositions.feeReplyKey {root : Exec.Deriv} {b : Devm}
    (r : MintRootCallPositions root b) (fork : CoveredFork root.sevm.benvStat.fork) :
    mintReplyRow r.fee.out ∈ mintTraceKeys root := by
  have env1 := r.second.returned_sevm.trans r.first.returned_sevm
  have mem0 := balanceRequestMemory_ptr getterInitMemory_ptr root.sevm.currentTarget
  have mem1 := balanceReplyMemory_ptr r.out0 mem0
  have mem2 := balanceRequestMemory_ptr mem1 r.first.call.returned.sevm.currentTarget
  have mem3 := balanceReplyMemory_ptr r.out1 mem2
  have actualCall := r.fee.occurrence.call.toStepIn
  simp only [r.fee.occurrence.input, r.fee.occurrence.sevm_eq, env1] at actualCall
  have member := mint_feeReply_mem fork mem3.wf actualCall
    ⟨1, _, r.fee.reply.stack, by decide⟩
  rw [r.fee.reply.returnData] at member
  exact member

/-- Existing trace-local separation discharges the fixed physical fee reply's
freshness. This projection preserves the original occurrence slot. -/
theorem mint_positional_source_finish {sevm : Sevm} {b post : Devm} {G : Nat}
    {K : WriterKey → Prop} {current : Checkpoint}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (r : MintRootCallPositions ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (fork : CoveredFork sevm.benvStat.fork)
    (inj : WriterInj (WriterExtend K
      (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart (WriterExtend K
      (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    MintPositionalSourceFinish K current invocation post r := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  have feeRow : WriterExtend K (mintTraceKeys root)
      (.balance (mintPositionalFeeWord r).toAdr) := Or.inr (r.feeReplyKey fork)
  have sub : ∀ k, K k → WriterExtend K (mintTraceKeys root) k := fun _ tracked => Or.inl tracked
  have rows : WriterExtend K (mintTraceKeys root) (.balance (0 : B256).toAdr) ∧
      WriterExtend K (mintTraceKeys root) (.balance (Sevm.dataWord sevm 4).toAdr) :=
    ⟨Or.inr (mintTraceKeys_rows root).1, Or.inr (mintTraceKeys_rows root).2⟩
  have freshFee := mint_feeFresh_of_universe inj apart sub feeRow
    {current.state with unlocked := 0} sevm (mintPositionalFeeBase r)
    (mintRootReserve0 root b) (mintRootReserve1 root b)
  have feeKeys := mint_feeKeys_sub sub feeRow {current.state with unlocked := 0}
    sevm (mintPositionalFeeBase r) (mintRootReserve0 root b) (mintRootReserve1 root b)
  have freshMint := mint_afterFeeFresh_of_universe inj apart feeKeys rows.1 rows.2
    (mintPositionalFeeResult current r).state
  exact r.sourceFinish rep invocation rfl fork freshFee freshMint

end Blanc.Lift.UniswapV2Pair
