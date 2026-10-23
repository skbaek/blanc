import Jaune.MemoryAccounting
import Blanc.MessageDelegationGas
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTransactionGas
import Blanc.ExecutionTraceCalldata

/-!
# The gas measure of every frame a configured history enters

Every raw frame of a configured history (`ConfiguredHistoryTrace.rawFrames`: the roots of every
frame actually entered, including those of subtrees that later revert) starts with a gas measure
below one word.  Nothing here depends on the fork's state-gas lane: the bound rests on Jaune's
step-level gas obligation `Evm.step_gasBound`, which says that a same-frame step strictly lowers
`gasMeasure`, and that a spawn hands its child a grant which, together with the measure the parent
retains, is strictly below the parent's measure before the spawn (the value charge covers the
stipend).  `Exec.rawFrameRoots_gasMeasure_le` turns that into "every entered frame starts at or
below the root's measure".  A root frame starts at exactly its message's grant
(`Frame.enter_run_gasMeasure`); a transaction's grant is its gas less the intrinsic charge, which
`checkTransaction` bounds by the block gas limit, itself bounded by `2 ^ 63` through the header
validation of the transition (`ConfiguredBlockTrace.header_gasLimit_lt`); a system message's grant
is the constant `systemTransactionGas`.
-/

namespace Blanc

open Jaune

/-! ### Every entered frame starts at or below the derivation root's measure -/

/-- A same-frame step strictly lowers the gas measure (`Evm.step_gasBound`, `cont` arm). -/
theorem Evm.step_cont_gasMeasure_lt {pc pc' : Nat} {sevm : Sevm} {pre d : Devm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' d) : d.gasMeasure < pre.gasMeasure := by
  have hb := Evm.step_gasBound ⟨pc, sevm, pre⟩
  rw [hstep] at hb
  exact hb

/-- A spawn hands its child a grant which, together with the measure the parent retains, is
strictly below the parent's measure before the step (`Evm.step_gasBound`, `spawn` arm). -/
theorem Evm.step_spawn_gas_lt {pc pc' : Nat} {sevm : Sevm} {pre : Devm} {f : Frame}
    {rsm : Resume} (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc') :
    f.inner.gas + rsm.parentGas < pre.gasMeasure := by
  have hb := Evm.step_gasBound ⟨pc, sevm, pre⟩
  rw [hstep] at hb
  exact hb.1

/-- **The gas measure of every entered frame is at most the root's.**  A same-frame step lowers
the measure, a spawned child starts at its grant, and a resumed parent gets back at most what it
retained plus what the child had left, all of which `Evm.step_gasBound` keeps below the measure
before the step. -/
theorem Exec.rawFrameRoots_gasMeasure_le {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ root ∈ Exec.rawFrameRoots run, root.devm.gasMeasure ≤ pre.gasMeasure := by
  induction run with
  | halt hstep =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact Nat.le_refl _
  | cont hstep next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl _
      · exact Nat.le_trans
          (ih root (by simp only [rawFrameRoots, List.mem_cons, member, or_true]))
          (Nat.le_of_lt (Evm.step_cont_gasMeasure_lt hstep))
  | doneErr hstep henter hresume =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact Nat.le_refl _
  | doneOk hstep henter hresume next ih =>
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl _
      · have hb := Evm.step_spawn_gas_lt hstep
        obtain ⟨child, hchild, hpost⟩ := Resume.run_ok_gasMeasure hresume
        have hle := Frame.enter_done_gasLe henter hchild
        have hroot := ih root (by simp only [rawFrameRoots, List.mem_cons, member, or_true])
        omega
  | runErr hstep henter child hresume ih =>
      intro root member
      have hb := Evm.step_spawn_gas_lt hstep
      have hgrant := Frame.enter_run_gasMeasure henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact Nat.le_refl _
      · dsimp only
        omega
      · have hroot := ih root (by simp only [rawFrameRoots, List.mem_cons, member, or_true])
        omega
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro root member
      have hb := Evm.step_spawn_gas_lt hstep
      have hgrant := Frame.enter_run_gasMeasure henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · exact Nat.le_refl _
      · dsimp only
        omega
      · have hroot := ihChild root (by simp only [rawFrameRoots, List.mem_cons, member, or_true])
        omega
      · obtain ⟨settled, hsettled, hpost⟩ := Resume.run_ok_gasMeasure hresume
        have hle := Frame.settle_gasLe (Exec.settledGasLe child) hsettled
        have hroot := ihNext root (by simp only [rawFrameRoots, List.mem_cons, member, or_true])
        omega

namespace ExecutionTrace

/-! ### Messages: every entered frame starts at or below the grant -/

/-- A retained slot's frames all start at or below the grant of the frame that entered it. -/
theorem RetainedXlot.rawFrames_gasMeasure_le
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out) :
    ∀ root ∈ retained.rawFrames, root.devm.gasMeasure ≤ frame.inner.gas := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hgrant : pre.gasMeasure = frame.inner.gas := Frame.enter_run_gasMeasure henter
      intro root member
      exact hgrant ▸ Exec.rawFrameRoots_gasMeasure_le run root member

theorem ProcessMessageTrace.rawFrames_gasMeasure_le
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas :=
  RetainedXlot.rawFrames_gasMeasure_le trace.retained trace.run

theorem ProcessCreateMessageTrace.rawFrames_gasMeasure_le
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas :=
  RetainedXlot.rawFrames_gasMeasure_le trace.retained trace.run

/- The delegation-prefix gas preservations live in `Blanc.LadderBase`
(`setDelegationStep_gas`, `setDelegationLoop_gas`, `setDelegation_gas`,
`messageCallDelegation_gas`). -/

/-- **Every frame a settled message call enters starts at or below the message's grant.** -/
theorem MessageCallTrace.rawFrames_gasMeasure_le
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ msg.gas := by
  cases trace with
  | createCollision => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.rawFrames_gasMeasure_le
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      intro root member
      have h := coreTrace.rawFrames_gasMeasure_le root member
      have hexec : (messageCallExecutionMessage delegated).gas = delegated.gas := by
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> rfl
      rw [hexec, messageCallDelegation_gas delegation] at h
      exact h

/-! ### Transactions, system messages, bodies, blocks, histories -/

/-- A transaction's frames start at or below the block gas limit: the grant is the transaction's
gas less the intrinsic charge, and `checkTransaction` fits that gas in the block's allowance. -/
theorem TransactionTrace.rawFrames_gasMeasure_le_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ benv.stat.blockGasLimit := by
  intro root member
  have h := trace.message.rawFrames_gasMeasure_le root member
  have hmsg := trace.msg_gas_noStateGas
  have hroom := trace.gas_le_remaining_noStateGas hfork
  omega

theorem TransactionTrace.rawFrames_gasMeasure_le
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ benv.stat.blockGasLimit :=
  trace.rawFrames_gasMeasure_le_noStateGas hfork.rules_stateGas_none

theorem ApplyTransactionsTrace.rawFrames_gasMeasure_le_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ benv.stat.blockGasLimit := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_gasMeasure_le_noStateGas hfork root member
      · exact ih hfork root member

theorem ApplyTransactionsTrace.rawFrames_gasMeasure_le
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ benv.stat.blockGasLimit :=
  trace.rawFrames_gasMeasure_le_noStateGas hfork.rules_stateGas_none

/-- A system message's frames start at or below the constant system grant. -/
theorem SystemMessageTrace.rawFrames_gasMeasure_le
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas :=
  trace.message.rawFrames_gasMeasure_le

theorem RequestsTrace.rawFrames_gasMeasure_le
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas := by
  intro root member
  simp only [RequestsTrace.rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rawFrames_gasMeasure_le root member
  · exact trace.consolidation.rawFrames_gasMeasure_le root member

/-- Every frame of a body starts below one word of gas once the block gas limit does. -/
theorem AppliedBodyTrace.rawFrames_gasMeasure_lt_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : benv.stat.rules.stateGas = none) (hlimit : benv.stat.blockGasLimit < 2 ^ 256) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 256 := by
  intro root member
  simp only [AppliedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · have h := trace.beacon.rawFrames_gasMeasure_le root member
    simp only [systemTransactionGas] at h
    omega
  · have h := trace.history.rawFrames_gasMeasure_le root member
    simp only [systemTransactionGas] at h
    omega
  · have h := trace.transactions.rawFrames_gasMeasure_le_noStateGas hfork root member
    change root.devm.gasMeasure ≤ benv.stat.blockGasLimit at h
    omega
  · have h := trace.requests.rawFrames_gasMeasure_le root member
    simp only [systemTransactionGas] at h
    omega

theorem AppliedBodyTrace.rawFrames_gasMeasure_lt
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) (hlimit : benv.stat.blockGasLimit < 2 ^ 256) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 256 :=
  trace.rawFrames_gasMeasure_lt_noStateGas hfork.rules_stateGas_none hlimit

/-- The header gas limit of a transitioned block is below `2 ^ 63`, so every frame of the block
starts below one word of gas. -/
theorem ConfiguredBlockTrace.rawFrames_gasMeasure_lt
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 256 := by
  have hlimit := trace.header_gasLimit_lt
  refine trace.bodyTrace.rawFrames_gasMeasure_lt trace.covered ?_
  change trace.block.header.gasLimit < 2 ^ 256
  omega

end ExecutionTrace

end Blanc

/-! ## F8  history gas (generic; what `usdc_neverSigner_pair` needs to call F7) -/

namespace Blanc.ExecutionTrace

open Jaune Blanc

/-- **Every raw frame of a configured history starts below one word of gas** (the transaction's
gas limit is a header-bounded word; a call grant never exceeds the caller's gas plus the stipend
the value charge covers). -/
theorem ConfiguredHistoryTrace.rawFrame_gas {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ G ∈ tr.rawFrames, G.devm.gasMeasure < 2 ^ 256 := by
  induction tr with
  | refl => intro G member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro G member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih G member
      · exact block.rawFrames_gasMeasure_lt G member

end Blanc.ExecutionTrace
