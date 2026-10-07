import Blanc.Lift.Weth9.ClosedKeys
import Blanc.Lift.Weth9.ClosedKeysBody
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

/-- The concrete context discharges actual retained-message entry and execution. -/
theorem deposit_context_execution {benv : Benv} {state : Jaune.State} {bout' : BlockOutput}
    (ctx : DepositTxContext benv)
    (trace : TransactionTrace benv BlockOutput.init depositTx 0 state bout') :
    ∃ after post, trace.msg.code = code ∧ CoveredFork after.stat.fork ∧
      (Frame.ofCall trace.msg).enter = .run (initEvm (trace.msg.withBenv after)) ∧
      exec (initEvm (trace.msg.withBenv after)) = .ok post ∧ post.error = none := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let R : Jaune.State → Msg → Benv → Devm → Prop := fun _ msg after post =>
    msg.code = code ∧ CoveredFork after.stat.fork ∧
    (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)) ∧
    exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none
  obtain ⟨debit, msg, after, post, msgEq, facts, _⟩ :=
    trace.root_frame_of_call_value_with_message (R := R) fork (by rfl) ctx.chain.symm
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
          obtain ⟨installed, covered, enter, post, execution, error, refund, _, _, _, _⟩ :=
            deposit_prepared_success ctx debit msg after hdebit hprepare hentry
          exact ⟨post, execution, error, by rw [refund],
            installed, covered, enter, execution, error⟩)
  rw [msgEq] at facts
  exact ⟨after, post, facts⟩

/-- The actual admitted deposit's raw traversal contains only its positive holder root. -/
theorem deposit_context_rawFrames {benv : Benv} {state : Jaune.State} {bout' : BlockOutput}
    (ctx : DepositTxContext benv)
    (trace : TransactionTrace benv BlockOutput.init depositTx 0 state bout') :
    ∃ root, trace.rawFrames = [root] ∧ root.sevm.currentTarget = contractAddress ∧
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data := by
  obtain ⟨after, post, installed, fork, enter, execution, _⟩ :=
    deposit_context_execution ctx trace
  exact deposit_transaction_rawFrames trace ctx.chain after enter execution installed fork
    (by rw [installed]; exact getDelegatedCodeAddress_code)

/-- The actual body has finite deposit metadata, a genuine holder root, and a settled positive call. -/
theorem deposit_context_body_frames {st post : Jaune.State} {txBout bodyBout : BlockOutput}
    (trace : AppliedBodyTrace (input st) [.inr depositTx] [] post bodyBout)
    (ctx : DepositTxContext (input st))
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes post)
    (transaction : processTransaction (input st) .init depositTx 0 = .ok (post, txBout)) :
    (∀ visited ∈ trace.rawFrames, visited.sevm.currentTarget = contractAddress →
      visited.sevm.caller = senderE ∧ visited.sevm.data = depositTx.data) ∧
    (∃ root ∈ trace.rawFrames, root.sevm.currentTarget = contractAddress ∧
      root.sevm.caller = senderE) ∧
    (∃ frame ∈ trace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧ decodeCall frame.sevm = some (.deposit senderE amount)) := by
  obtain ⟨_, _, prefixEq⟩ := deposit_body_prefix trace beforeCodes
  have actualCtx : DepositTxContext
      (((input st).withState trace.beaconState).withState trace.historyState) := by
    rw [prefixEq]
    exact ctx
  obtain ⟨root, roots, target, caller, data⟩ :=
    deposit_fold_rawFrames trace.transactions (deposit_body_decoded trace)
      (fun _ _ head => deposit_context_rawFrames actualCtx head)
  obtain ⟨beacon, history, withdrawal, consolidation⟩ :=
    deposit_body_system_codes trace beforeCodes afterCodes transaction
  obtain ⟨metadata, member⟩ := deposit_body_roots trace roots caller data
    beacon history withdrawal consolidation
  refine ⟨metadata, ⟨root, member, target, caller⟩, ?_⟩
  exact deposit_body_settledFrame trace
    (fun _ _ head => deposit_context_settledFrame actualCtx head)

end Blanc.Lift.Weth9.ClosedInstance
