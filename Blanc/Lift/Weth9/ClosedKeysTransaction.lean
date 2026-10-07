import Blanc.Lift.Weth9.ClosedKeys
import Blanc.Lift.Weth9.ClosedDepositTxPrepared
import Blanc.ExecutionTraceRootFrame

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Every retained admitted deposit under the concrete world context has a genuine committed root. -/
theorem deposit_context_settledFrame {benv : Benv} {state : Jaune.State} {bout' : BlockOutput}
    (ctx : DepositTxContext benv)
    (trace : TransactionTrace benv BlockOutput.init depositTx 0 state bout') :
    ∃ frame ∈ trace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧ decodeCall frame.sevm = some (.deposit senderE amount) := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let R : Jaune.State → Msg → Benv → Devm → Prop := fun _ msg after _ =>
    (initSevm (msg.withBenv after)).currentTarget = contractAddress ∧
    (initSevm (msg.withBenv after)).isStatic = false ∧
    decodeCall (initSevm (msg.withBenv after)) = some (.deposit senderE amount)
  obtain ⟨debit, msg, after, post, facts, frame, member, _, sevmEq, _, _⟩ :=
    trace.root_frame_of_call_value (R := R) fork (by rfl) ctx.chain.symm
      (by decide) (by rw [ctx.baseFee]; decide)
      (deposit_intrinsic (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by decide) (CoveredFork.checkTransactionGasCap_ok fork (by decide))
      (by decide +kernel) ctx.room
      (by rw [ctx.chain]; exact depositTx_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode senderE).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by change 400001 ≤ (benv.state.bal senderE).toNat
          rw [ctx.balance]; decide +kernel)
      (by rw [ctx.code]; exact getDelegatedCodeAddress_code)
      (by unfold BenvStat.rules; rw [ctx.fork]; decide +kernel)
      (by intro debit msg after hdebit hprepare hentry
          obtain ⟨_, _, _, post, execution, error, refund, _, _, _, _⟩ :=
            deposit_prepared_success ctx debit msg after hdebit hprepare hentry
          refine ⟨post, execution, error, by rw [refund], ?_⟩
          have prepared := prepareMessage_call
            (benv := { benv.beginTransaction with state := debit })
            (tenv := transactionTenv benv.beginTransaction depositTx 0 senderE
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21064 [])
            (tx := depositTx) (t := contractAddress) (by rfl)
          have msgEq := Except.ok.inj (hprepare.symm.trans prepared)
          change (initSevm (msg.withBenv after)).currentTarget = contractAddress ∧
            (initSevm (msg.withBenv after)).isStatic = false ∧
            decodeCall (initSevm (msg.withBenv after)) = some (.deposit senderE amount)
          rw [msgEq]
          refine ⟨rfl, rfl, ?_⟩
          exact deposit_decodeCall rfl)
  refine ⟨frame, member, ?_⟩
  rw [sevmEq]
  exact facts

end Blanc.Lift.Weth9.ClosedInstance
