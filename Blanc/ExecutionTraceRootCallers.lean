import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionAccountingAdmission
import Blanc.Lift.CallerProvenance

/-!
# A contract never originates a settled message root

Every settled message root of a configured history is entered by the message's own caller: a
transaction root by its checked sender, a system root by `systemAddress`.  For an address `ca`
whose contract invariant holds at the checkpoint and is preserved by its admitted frames (so its
code stays installed at every transaction's begin state), EIP-3607 makes `ca` no sender
(`TransactionTrace.sender_ne_sem`); with `ca ≠ systemAddress`, `ca` is the caller of no settled
root (`ConfiguredHistoryTrace.settledRoots_caller_ne`).  Contract-neutral.
-/

namespace Blanc.ExecutionTrace

open Jaune ContractSpecSem

variable {c : ContractSpecSem}

theorem ProcessMessageTrace.settledRoots_caller {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (trace : ProcessMessageTrace msg out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre raw run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      · rw [List.mem_singleton] at member
        subst member
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entryBenv, -, evmEq⟩
        simp only [Frame.ofCall] at evmEq
        have sevmEq : sevm = initSevm (msg.withBenv entryBenv) := congrArg Evm.sta evmEq
        change sevm.caller = msg.caller
        rw [sevmEq]
        rfl
      · cases member
    · cases member

theorem ProcessCreateMessageTrace.settledRoots_caller {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre raw run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · simp only [RetainedXlot.settledRoots] at member
      split at member
      · rw [List.mem_singleton] at member
        subst member
        have enter := (RunFrame.some_inv process).1
        rcases Frame.enter_run_inv enter with ⟨entryBenv, -, evmEq⟩
        simp only [Frame.ofCreate] at evmEq
        have sevmEq : sevm = initSevm ((processCreateMessage.msg msg).withBenv entryBenv) :=
          congrArg Evm.sta evmEq
        change sevm.caller = msg.caller
        rw [sevmEq]
        rfl
      · cases member
    · cases member

theorem MessageCallTrace.settledRoots_caller {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = msg.caller := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun targetNone collision evm core inner result =>
    exact inner.settledRoots_caller
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm core inner result =>
    intro R member
    rw [inner.settledRoots_caller R member, execMsgEq, messageCallExecutionMessage_caller_eq,
      messageCallDelegation_caller_eq delegation]

theorem SystemMessageTrace.settledRoots_caller {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  intro R member
  rw [trace.message.settledRoots_caller R member, systemTransactionMessage_caller]

theorem RequestsTrace.settledRoots_caller {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  intro R member
  rcases List.mem_append.mp member with member | member
  · exact trace.withdrawal.settledRoots_caller R member
  · exact trace.consolidation.settledRoots_caller R member

theorem TransactionTrace.settledRoots_caller_ne {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : c.StateInv ca benv.state) (notCreated : ca ∉ benv.createdAccounts) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca := by
  intro R member
  rw [trace.message.settledRoots_caller R member, trace.msg_caller]
  exact trace.sender_ne_sem inv notCreated

theorem ApplyTransactionsTrace.settledRoots_caller_ne {ca : Adr} {entry : Sevm → Devm → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmitted ca entry) (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry) (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca := by
  induction trace with
  | nil => intro R member; cases member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
    have headInv : c.BenvInv ca (benv.withState txState) :=
      head.benvInv_admitted_sem preserves hfork admitted.1 sumNof inv
    have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
      Nat.lt_of_le_of_lt
        (by simpa only [Benv.withState] using
          processTransaction_sum_le head.result hfork.rules_stateGas_none)
        sumNof
    intro R member
    rcases List.mem_append.mp member with member | member
    · exact head.settledRoots_caller_ne inv.state inv.ca R member
    · exact ih (by simpa only [Benv.withState] using hfork) admitted.2 nextSum headInv R member

theorem AppliedBodyTrace.settledRoots_caller_ne {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (preserves : c.PreservesAdmitted ca entry) (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv) (notSystem : ca ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_sem
    preserves hfork admitted.beacon inv
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_sem
    preserves (by simpa only [Benv.withState] using hfork) admitted.history beaconInv
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have : sum trace.historyState.bal ≤ sum benv.state.bal :=
      le_trans (by simpa only [Benv.withState] using history.2) beacon.2
    omega
  have systemNe : systemAddress ≠ ca := fun h => notSystem h.symm
  intro R member
  simp only [AppliedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · rw [trace.beacon.settledRoots_caller R member]
    exact systemNe
  · rw [trace.history.settledRoots_caller R member]
    exact systemNe
  · exact trace.transactions.settledRoots_caller_ne preserves
      (by simpa only [Benv.withState] using hfork) admitted.transactions historySum historyInv
      R member
  · rw [trace.requests.settledRoots_caller R member]
    exact systemNe

/-- **A contract never originates a settled message root.**  If the contract invariant of `ca`
holds at the checkpoint and its admitted frames preserve it, and `ca` is not the system address,
then `ca` is the caller of no settled root of the history. -/
theorem ConfiguredHistoryTrace.settledRoots_caller_ne {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (preserves : c.PreservesAdmitted ca entry) (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) (notSystem : ca ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca := by
  induction trace with
  | refl => intro R member; cases member
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with member | member
    · exact ih admitted.1 R member
    · have blockInv := prior.stateInv_admitted_sem preserves admitted.1 inv
      exact block.bodyTrace.settledRoots_caller_ne preserves block.covered admitted.2
        block.openingBound ⟨blockInv, block.not_mem_openingCreatedAccounts ca⟩ notSystem R member

end Blanc.ExecutionTrace
