import Blanc.Composition.UniswapV2PairWeth9CapstoneTx2Raw
import Blanc.Composition.UniswapV2PairWeth9SigningTx1Recover
import Blanc.Composition.UniswapV2PairWeth9SigningTx2Recover
import Blanc.ExecutionTraceRootFrame
import Blanc.ForwardCall

/-!
# The raw frames of the closed instance's two transaction traces

`tx1_trace_raw`: every raw frame of a trace of `signedTx1` (on a `Tx1Context` environment) runs at
`X`: Token20's frame enters nothing.  `tx2_trace_raw`: the raw frames of a trace of `signedTx2` (on a
`Tx2Context` environment) are the raw roots of one run of the Pair's swap frame from an entry
satisfying U10b's `Tx2Frame`, so `tx2_swap_raw` describes them.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Composition.UniswapV2PairWeth9Instance

/-- **`tx2`'s trace enters exactly the swap frame's raw roots.** -/
theorem tx2_trace_raw {benv : Benv} (ctx : Tx2Context benv) {bout : BlockOutput}
    (hused : bout.blockGasUsed = 31757) {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout signedTx2 1 state bout') :
    ∃ (sevm : Sevm) (b : Devm) (G : Nat) (_ : Tx2Frame sevm (St b [] Mem.empty G))
      (out : Execution) (run : Exec 0 sevm (St b [] Mem.empty G) out),
      trace.rawFrames = Exec.rawFrameRoots run := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let R : Jaune.State → Msg → Benv → Devm → Prop := fun _ msg after _ =>
    Tx2Frame (initSevm (msg.withBenv after)) (initDevm (msg.withBenv after)) ∧
    (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)) ∧
    msg.target.isNone = false ∧ msg.tenv.stat.auths.isEmpty = true ∧
    getDelegatedCodeAddress msg.code = none
  obtain ⟨debit, msg, after, post, msgEq, ⟨frame, enter, target, auths, nodeleg⟩, -⟩ :=
    trace.root_frame_of_call_value_with_message (R := R) (E := trader) (t := pair) (chainId := 1)
      (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21980) (calldataFloorGas := 23450)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (tx2_intrinsic 1 tx2SigR tx2SigS (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [show signedTx2.gas = 300000 from rfl]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork (by rw [show signedTx2.gas = 300000 from rfl]; decide))
      (by change (1 : UInt64) ≠ UInt64.max; decide)
      (by rw [show signedTx2.gas = 300000 from rfl, hused]; have := ctx.room; omega)
      (by rw [ctx.chain]; exact tx2_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [show signedTx2.gas = 300000 from rfl, show signedTx2.value = 0 from rfl,
            show (benv.state.get trader).bal = 9936486 from ctx.balance]
          decide +kernel)
      (by rw [ctx.pairCode]; exact getDelegatedCodeAddress_pair)
      (by rw [rules_bpo2 ctx.fork]; decide +kernel)
      (by
        intro debit msg after hdebit hprepare hentry
        obtain ⟨frame, -⟩ := tx2_prepared_frame ctx 1 tx2SigR tx2SigS debit msg after hdebit
          hprepare hentry
        obtain ⟨post, execution, -, error, refund, -, -, -⟩ := tx2_frame_success frame
        have msgEq := Except.ok.inj (hprepare.symm.trans (prepareMessage_call (by rfl)))
        subst msgEq
        refine ⟨post, execution, error, by rw [refund]; decide, frame, ?_, rfl, rfl, ?_⟩
        · refine Frame.enter_run_of_nonprecompile hentry (adr := pair) rfl ?_
          change after.stat.rules.isPrecomp pair = false
          rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hentry
          obtain rfl := (Except.ok.inj hentry).symm
          change benv.stat.rules.isPrecomp pair = false
          rw [rules_bpo2 ctx.fork]
          decide +kernel
        · exact (congrArg getDelegatedCodeAddress frame.code).trans getDelegatedCodeAddress_pair)
  subst msgEq
  obtain ⟨raw, run, frames⟩ :=
    messageCallTrace_rawFrames_run trace.message target auths nodeleg enter
  exact ⟨initSevm (trace.msg.withBenv after), initDevm (trace.msg.withBenv after),
    (trace.msg.withBenv after).gas, frame, raw, run, frames⟩

/-- **Every raw frame of `tx1`'s trace runs at `X`.** -/
theorem tx1_trace_raw {benv : Benv} {xT xP : B256} (ctx : Tx1Context benv xT xP)
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv BlockOutput.init signedTx1 0 state bout') :
    ∀ d ∈ trace.rawFrames, d.sevm.currentTarget = tokenX := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let R : Jaune.State → Msg → Benv → Devm → Prop := fun _ msg after _ =>
    (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)) ∧
    msg.target.isNone = false ∧ msg.tenv.stat.auths.isEmpty = true ∧
    msg.code = VyperNonreentrantDeployed.Token20.code ∧ msg.currentTarget = tokenX
  obtain ⟨debit, msg, after, post, msgEq, ⟨enter, target, auths, code, current⟩, -⟩ :=
    trace.root_frame_of_call_value_with_message (R := R) (E := trader) (t := tokenX)
      (chainId := 1) (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21584)
      (calldataFloorGas := 22460)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (tx1_intrinsic 1 tx1SigR tx1SigS (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [show signedTx1.gas = 50000 from rfl]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork (by rw [show signedTx1.gas = 50000 from rfl]; decide))
      (by change (0 : UInt64) ≠ UInt64.max; decide)
      (by change 50000 ≤ benv.stat.blockGasLimit - 0; have := ctx.room; omega)
      (by rw [ctx.chain]; exact tx1_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [show signedTx1.gas = 50000 from rfl, show signedTx1.value = 0 from rfl,
            show (benv.state.get trader).bal = 10000000 from ctx.balance]
          decide +kernel)
      (by rw [ctx.code]; exact getDelegatedCodeAddress_token20)
      (by unfold BenvStat.rules; rw [ctx.fork]; decide +kernel)
      (by
        intro debit msg after hdebit hprepare hentry
        obtain ⟨post, execution, error, refund, -, -, -, -⟩ :=
          tx1_prepared_success ctx 1 tx1SigR tx1SigS debit msg after hdebit hprepare hentry
        have debitCode : debit.getCode tokenX = VyperNonreentrantDeployed.Token20.code := by
          obtain ⟨_, equation⟩ := State.of_subBal hdebit
          rw [equation, State.setBal_getCode]
          exact State.incrNonce_get_code.trans ctx.code
        have msgEq := Except.ok.inj (hprepare.symm.trans (prepareMessage_call (by rfl)))
        subst msgEq
        refine ⟨post, execution, error, by rw [refund], ?_, rfl, rfl, debitCode, rfl⟩
        refine Frame.enter_run_of_nonprecompile hentry (adr := tokenX) rfl ?_
        change after.stat.rules.isPrecomp tokenX = false
        rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hentry
        obtain rfl := (Except.ok.inj hentry).symm
        change benv.stat.rules.isPrecomp tokenX = false
        unfold BenvStat.rules; rw [ctx.fork]; decide +kernel)
  subst msgEq
  obtain ⟨raw, run, frames⟩ := messageCallTrace_rawFrames_run trace.message target auths
    (by rw [code]; exact getDelegatedCodeAddress_token20) enter
  have nil := token20_rawFrameDescendants_nil run code
  intro d member
  change d ∈ trace.message.rawFrames at member
  rw [frames] at member
  obtain ⟨-, dsevm, -⟩ := eq_root_of_rawFrameDescendants_nil run nil member
  rw [dsevm]
  exact current

end Blanc.Composition.UniswapV2PairWeth9Capstone
