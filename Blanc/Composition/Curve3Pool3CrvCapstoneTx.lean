import Blanc.Composition.Curve3Pool3CrvCapstoneFrame
import Blanc.Composition.Curve3Pool3CrvSigningRecover
import Blanc.Composition.UniswapV2PairWeth9Tx2Receipts
import Blanc.Composition.UniswapV2PairWeth9CapstoneRaw
import Blanc.ExecutionTraceRootFrame
import Blanc.ExecutionTraceCodeKeep
import Blanc.Lift.LogAddresses

/-!
# U9(b): the signed `exchange` transaction succeeds

On any block environment satisfying `ExTxContext`:

* `ex_transaction`: processing `signedExchangeTx` as the block's first transaction succeeds, its
  receipt carries no deposit-contract log (so no deposit request), and it uses at most its gas
  limit — the root frame is `ex_frame_live` (`exchange_live` at the closed instance), whose logs
  come from the pool's and the coins' frames only (`Exec.log_addresses`);
* `ex_trace_raw`: any trace of that transaction enters exactly the raw roots of one exchange
  frame execution from an `ExFrame` entry.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint

section Tx

variable {benv : Benv} (ctx : ExTxContext benv)
include ctx

theorem ex_fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2

theorem ex_poolNotPrecomp : benv.stat.rules.isPrecomp poolAddr = false := by
  rw [ex_rules_bpo2 ctx.fork]
  exact prec_false (by decide +kernel)

end Tx

/-- **The exchange frame's logs** come from the pool and the coins: none from the deposit
contract. -/
theorem ex_frame_logs {sevm : Sevm} {b post : Devm} (hf : ExFrame sevm b)
    (exc : Exec 0 sevm b (.ok post)) (herr : post.error = none) (hlogs : b.logs = []) :
    ∀ log ∈ post.logs, log.address ≠ depositContractAddress := by
  intro log hlog
  have hc : Execution.commits (.ok post : Execution) = true := by
    simp only [Execution.commits, herr, Option.isNone_none]
  rcases Exec.log_addresses exc hc (exFrame_fork hf) log hlog with h | ⟨r, hr, ha⟩
  · rw [hlogs] at h
    cases h
  · rw [ha]
    rcases List.mem_cons.mp hr with rfl | hd
    · show sevm.currentTarget ≠ _
      rw [hf.target]
      decide +kernel
    · obtain ⟨c, -, ⟨k, hk⟩, hrs, -, -⟩ := exFrame_raw hf exc r hd
      rw [hrs, hk]
      show exCoin sevm b k ≠ _
      rw [exFrame_coin hf k]
      match k with
      | 0 => decide +kernel
      | 1 => decide +kernel
      | 2 => decide +kernel

section Run

variable {benv : Benv} (ctx : ExTxContext benv)
include ctx

/-- **The signed exchange transaction succeeds** as the block's first transaction: its receipt
logs no deposit, it uses at most its gas limit. -/
theorem ex_transaction :
    ∃ (s1 : Jaune.State) (bout : BlockOutput),
      processTransaction benv BlockOutput.init signedExchangeTx 0 = .ok (s1, bout) ∧
      parseDepositRequests bout = .ok [] ∧ bout.blockGasUsed ≤ 1000000 := by
  have fork := ex_fork ctx
  let Q : Jaune.State → Devm → Prop := fun _ post =>
    ∀ log ∈ post.logs, log.address ≠ depositContractAddress
  obtain ⟨debit, post, bout', hq, process, -, gas, keys, receipt, -⟩ :=
    processTransaction_call_value_of_exec_receipts_frame (Q := Q) (bout := BlockOutput.init)
      (tx := signedExchangeTx) (E := trader) (t := poolAddr) (chainId := 1)
      (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21600)
      (calldataFloorGas := 22500) (index := 0)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (ex_intrinsic 1 exchangeSigR exchangeSigS (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [show signedExchangeTx.gas = 900000 from rfl]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork
        (by rw [show signedExchangeTx.gas = 900000 from rfl]; decide))
      (by change (0 : UInt64) ≠ UInt64.max; decide)
      (by rw [show signedExchangeTx.gas = 900000 from rfl]; have := ctx.room
          change 900000 ≤ benv.stat.blockGasLimit - 0; omega)
      (by rw [ctx.chain]; exact exchange_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [show signedExchangeTx.gas = 900000 from rfl, show signedExchangeTx.value = 0 from rfl,
            show (benv.state.get trader).bal = traderEther from ctx.balance]
          decide +kernel)
      (by rw [ctx.poolCode]; exact getDelegatedCodeAddress_pool)
      (ex_poolNotPrecomp ctx)
      (by
        intro debit msg after hdebit hprepare hentry
        obtain ⟨frame, -⟩ := ex_prepared_frame ctx 1 exchangeSigR exchangeSigS debit msg after
          hdebit hprepare hentry
        obtain ⟨post, exc, -, -, -, -, -, herr, hrefund⟩ := ex_frame_live frame
        exact ⟨post, (exec_iff_exec_eq 0 _ _ (.ok post)).mp ⟨exc⟩, herr, hrefund,
          ex_frame_logs frame exc herr
            (Lift.initDevm_logs (exFrame_fork frame).rules_stateGas_none)⟩)
  refine ⟨_, bout', process, ?_, ?_⟩
  · apply BlockForward.parseDepositRequests_of_no_deposit_logs
    intro key member
    rw [keys] at member
    simp only [BlockOutput.init, List.nil_append, List.mem_singleton] at member
    subst member
    exact ⟨_, receipt, hq⟩
  · rw [gas]
    change 0 + _ ≤ 1000000
    have := txGasUsed_le (gas := signedExchangeTx.gas) (floor := 22500) (left := post.gasLeft)
      (refund := post.refundCounter.toNat) (by decide)
    have hg : signedExchangeTx.gas = 900000 := rfl
    omega

/-- **The exchange transaction's trace enters exactly the raw roots of one exchange frame
execution** from an `ExFrame` entry. -/
theorem ex_trace_raw {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv BlockOutput.init signedExchangeTx 0 state bout') :
    ∃ (sevm : Sevm) (b post : Devm) (_ : ExFrame sevm b) (exc : Exec 0 sevm b (.ok post)),
      trace.rawFrames = Exec.rawFrameRoots exc := by
  have fork := ex_fork ctx
  let R : Jaune.State → Msg → Benv → Devm → Prop := fun _ msg after _ =>
    ExFrame (initSevm (msg.withBenv after)) (initDevm (msg.withBenv after)) ∧
    (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)) ∧
    msg.target.isNone = false ∧ msg.tenv.stat.auths.isEmpty = true ∧
    getDelegatedCodeAddress msg.code = none
  obtain ⟨debit, msg, after, post, msgEq, ⟨frame, enter, target, auths, nodeleg⟩, -⟩ :=
    trace.root_frame_of_call_value_with_message (R := R) (E := trader) (t := poolAddr)
      (chainId := 1) (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21600)
      (calldataFloorGas := 22500)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (ex_intrinsic 1 exchangeSigR exchangeSigS (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [show signedExchangeTx.gas = 900000 from rfl]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork
        (by rw [show signedExchangeTx.gas = 900000 from rfl]; decide))
      (by change (0 : UInt64) ≠ UInt64.max; decide)
      (by rw [show signedExchangeTx.gas = 900000 from rfl]; have := ctx.room
          change 900000 ≤ benv.stat.blockGasLimit - 0; omega)
      (by rw [ctx.chain]; exact exchange_recoveredSender)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [show signedExchangeTx.gas = 900000 from rfl, show signedExchangeTx.value = 0 from rfl,
            show (benv.state.get trader).bal = traderEther from ctx.balance]
          decide +kernel)
      (by rw [ctx.poolCode]; exact getDelegatedCodeAddress_pool)
      (ex_poolNotPrecomp ctx)
      (by
        intro debit msg after hdebit hprepare hentry
        obtain ⟨frame, -⟩ := ex_prepared_frame ctx 1 exchangeSigR exchangeSigS debit msg after
          hdebit hprepare hentry
        obtain ⟨post, exc, -, -, -, -, -, herr, hrefund⟩ := ex_frame_live frame
        have msgEq := Except.ok.inj (hprepare.symm.trans (prepareMessage_call (by rfl)))
        subst msgEq
        refine ⟨post, (exec_iff_exec_eq 0 _ _ (.ok post)).mp ⟨exc⟩, herr, hrefund, frame, ?_, rfl,
          rfl, ?_⟩
        · refine Frame.enter_run_of_nonprecompile hentry (adr := poolAddr) rfl ?_
          change after.stat.rules.isPrecomp poolAddr = false
          rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hentry
          obtain rfl := (Except.ok.inj hentry).symm
          change benv.stat.rules.isPrecomp poolAddr = false
          exact ex_poolNotPrecomp ctx
        · exact (congrArg getDelegatedCodeAddress frame.code).trans getDelegatedCodeAddress_pool)
  subst msgEq
  obtain ⟨raw, run, frames⟩ :=
    UniswapV2PairWeth9Capstone.messageCallTrace_rawFrames_run trace.message target auths nodeleg
      enter
  obtain ⟨post', exc, -⟩ := ex_frame_live frame
  have h1 := (exec_iff_exec_eq _ _ _ raw).mp ⟨run⟩
  have h2 := (exec_iff_exec_eq 0 _ _ (.ok post')).mp ⟨exc⟩
  have hraw : raw = .ok post' := h1.symm.trans h2
  subst hraw
  exact ⟨_, _, _, frame, run, frames⟩

end Run

end Blanc.Composition.Curve3Pool3CrvInstance
