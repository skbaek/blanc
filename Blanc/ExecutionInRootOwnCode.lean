import Blanc.ExecutionInRawNodeOrigin
import Blanc.ExecutionInCodeImage
import Blanc.ExecutionCallerExclusion

/-! Own code and code addresses at actual complete-settlement outer roots. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Actual own-code and code-address provenance at a message root. The condition
excludes creation roots at an already-code-bearing address and delegation
resolution to a different code address. -/
def RootOwnEntry (n : Exec.Deriv) : Prop :=
  ∀ wa, n.sevm.currentTarget = wa → (n.devm.getCode wa).toList ≠ [] →
    ¬ isValidDelegation (n.devm.getCode wa) →
      n.sevm.code = n.devm.getCode wa ∧ n.sevm.codeAddress = some wa

theorem RootOwnEntry.code {n : Exec.Deriv} (entry : RootOwnEntry n) : RootOwnCode n :=
  fun wa target nonempty notDelegation => (entry wa target nonempty notDelegation).1

/-- The message-level producer of both root code and its original code address. -/
def MsgRootEntry (msg : Msg) : Prop :=
  ∀ wa, msg.currentTarget = wa → (msg.benv.state.getCode wa).toList ≠ [] →
    ¬ isValidDelegation (msg.benv.state.getCode wa) →
      msg.code = msg.benv.state.getCode wa ∧ msg.codeAddress = some wa

theorem Frame.enter_run_rootOwnEntry {frame : Frame} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {execution : Execution} (run : Exec pc sevm pre execution)
    (enter : frame.enter = .run ⟨pc, sevm, pre⟩) (root : MsgRootEntry frame.inner) :
    RootOwnEntry ⟨pc, sevm, pre, execution, run⟩ := by
  intro wa target nonempty notDelegation
  have actual := root wa
    ((Frame.enter_run_currentTarget enter).symm.trans target)
    (by rw [← Frame.enter_run_getCode enter]; exact nonempty)
    (by rw [← Frame.enter_run_getCode enter]; exact notDelegation)
  exact ⟨(Frame.enter_run_code enter).trans
    (actual.1.trans (Frame.enter_run_getCode enter wa).symm),
    (Frame.enter_run_codeAddress enter).trans actual.2⟩

/-- The collision check excludes a creation root at a nonempty installed address. -/
theorem processCreateMessage_msg_rootEntry {msg : Msg}
    (collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false) :
    MsgRootEntry (processCreateMessage.msg msg) := by
  intro wa target nonempty _
  have nonempty' : (msg.benv.state.getCode wa).toList ≠ [] := by
    rw [← processCreateMessage.msg_getCode msg wa]
    exact nonempty
  exact absurd target (ne_wa_of_not_hasCodeOrNonce nonempty' collision)

/-- Authorization preserves the original code-address field; non-designating
own code makes subsequent code resolution retain that same address. -/
theorem messageCallExecutionMessage_rootEntry {msg : Msg}
    (own : msg.code = msg.benv.state.getCode msg.currentTarget)
    (address : msg.codeAddress = some msg.currentTarget) :
    MsgRootEntry (messageCallExecutionMessage msg) := by
  intro wa target nonempty notDelegation
  refine ⟨messageCallExecutionMessage_rootCode own wa target nonempty notDelegation, ?_⟩
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation at target notDelegation ⊢
  split
  · rename_i none
    rw [none] at target
    exact address.trans (congrArg some target)
  · rename_i adr resolved
    rw [resolved] at target notDelegation
    exfalso
    apply notDelegation
    rw [← target, ← own]
    unfold ForkRules.delegatedCodeAddress at resolved
    split at resolved
    · unfold getDelegatedCodeAddress at resolved
      split at resolved
      · assumption
      · cases resolved
    · cases resolved

/-- A retained slot's committed root keeps the actual message-entry own-code fact. -/
theorem RetainedXlot.settledRoots_rootOwnEntry {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : RunFrame frame slot out) (root : MsgRootEntry frame.inner) :
    ∀ R ∈ retained.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre execution run =>
    intro R member
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      exact Frame.enter_run_rootOwnEntry run (RunFrame.some_inv process).1 root
    · cases member

theorem ProcessMessageTrace.settledRoots_rootOwnEntry {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (root : MsgRootEntry msg) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  rcases trace with ⟨slot, retained, process⟩
  have own := retained.settledRoots_rootOwnEntry process root
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact own R member
    · cases member

theorem ProcessCreateMessageTrace.settledRoots_rootOwnEntry {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  rcases trace with ⟨slot, retained, process⟩
  have own := retained.settledRoots_rootOwnEntry process
    (processCreateMessage_msg_rootEntry collision)
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · exact own R member
    · cases member

/-- Only the actual outer roots are selected; delegated descendants are not included. -/
theorem MessageCallTrace.settledRoots_rootOwnEntry {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out) (own : MsgOwn msg) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun target collision evm core inner result =>
    exact inner.settledRoots_rootOwnEntry (by simpa only [messageCreateCollision] using collision)
  | callRun target delegated refund delegation execMsg execEq evm core inner result =>
    subst execEq
    exact inner.settledRoots_rootOwnEntry
      (messageCallExecutionMessage_rootEntry (messageCallDelegation_own delegation target own)
        (by
          rw [(messageCallDelegation_fields delegation).2.2.2.2.2,
            (messageCallDelegation_fields delegation).2.2.1]
          exact (own target).1))

theorem TransactionTrace.settledRoots_rootOwnEntry {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) :=
  trace.message.settledRoots_rootOwnEntry (prepareMessage_own_entry trace.prepared)

theorem ApplyTransactionsTrace.settledRoots_rootOwnEntry
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  induction trace with
  | nil => intro R member; cases member
  | cons head tail ih =>
    intro R member
    rcases List.mem_append.mp member with here | later
    · exact head.settledRoots_rootOwnEntry R here
    · exact ih R later

theorem SystemMessageTrace.settledRoots_rootOwnEntry {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) :=
  trace.message.settledRoots_rootOwnEntry fun _ => ⟨rfl, rfl⟩

theorem RequestsTrace.settledRoots_rootOwnEntry {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  intro R member
  rcases List.mem_append.mp member with withdrawal | consolidation
  · exact trace.withdrawal.settledRoots_rootOwnEntry R withdrawal
  · exact trace.consolidation.settledRoots_rootOwnEntry R consolidation

theorem BeaconStageTrace.settledRoots_rootOwnEntry {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ message _ _ => exact message.settledRoots_rootOwnEntry

theorem HistoryStageTrace.settledRoots_rootOwnEntry {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ _ _ message _ _ => exact message.settledRoots_rootOwnEntry

theorem RequestStageTrace.settledRoots_rootOwnEntry {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ requests _ => exact requests.settledRoots_rootOwnEntry

theorem StagedBodyTrace.settledRoots_rootOwnEntry {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  intro R member
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((beacon | history) | transaction) | request
  · exact trace.beacon.settledRoots_rootOwnEntry R beacon
  · exact trace.history.settledRoots_rootOwnEntry R history
  · exact trace.transactions.settledRoots_rootOwnEntry R transaction
  · exact trace.requests.settledRoots_rootOwnEntry R request

theorem ConfiguredBlockTraceIn.settledRoots_rootOwnEntry {F : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ R ∈ trace.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) :=
  trace.bodyTrace.settledRoots_rootOwnEntry

/-- Every actual settled outer root runs its entry code whenever that code is
nonempty and nondelegating. This conditional equality needs no installed-world
invariant or extra stage capability. -/
theorem ConfiguredHistoryTraceIn.settledRoots_rootOwnEntry {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ R ∈ history.settledRoots, RootOwnEntry (Exec.Frame.rootDeriv R) := by
  induction history with
  | refl => intro R member; cases member
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with earlier | inBlock
    · exact ih R earlier
    · exact block.settledRoots_rootOwnEntry R inBlock

/-- A retained slot's committed root keeps the actual message-entry own-code fact. -/
theorem RetainedXlot.settledRoots_rootOwnCode {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : RunFrame frame slot out) (root : MsgRootCode frame.inner) :
    ∀ R ∈ retained.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  cases retained with
  | none => intro R member; cases member
  | @some pc sevm pre execution run =>
    intro R member
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      exact Frame.enter_run_rootOwnCode run (RunFrame.some_inv process).1 root
    · cases member

theorem ProcessMessageTrace.settledRoots_rootOwnCode {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (root : MsgRootCode msg) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  rcases trace with ⟨slot, retained, process⟩
  have own := retained.settledRoots_rootOwnCode process root
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact own R member
    · cases member

theorem ProcessCreateMessageTrace.settledRoots_rootOwnCode {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (ProcessCreateMessageTrace.settledRoots_rootOwnEntry trace collision R member).code

theorem MessageCallTrace.settledRoots_rootOwnCode {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out) (own : MsgOwn msg) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (MessageCallTrace.settledRoots_rootOwnEntry trace own R member).code

theorem TransactionTrace.settledRoots_rootOwnCode {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (TransactionTrace.settledRoots_rootOwnEntry trace R member).code

theorem ApplyTransactionsTrace.settledRoots_rootOwnCode
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (ApplyTransactionsTrace.settledRoots_rootOwnEntry trace R member).code

theorem SystemMessageTrace.settledRoots_rootOwnCode {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (SystemMessageTrace.settledRoots_rootOwnEntry trace R member).code

theorem RequestsTrace.settledRoots_rootOwnCode {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (RequestsTrace.settledRoots_rootOwnEntry trace R member).code

theorem BeaconStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (BeaconStageTrace.settledRoots_rootOwnEntry trace R member).code

theorem HistoryStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (HistoryStageTrace.settledRoots_rootOwnEntry trace R member).code

theorem RequestStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (RequestStageTrace.settledRoots_rootOwnEntry trace R member).code

theorem StagedBodyTrace.settledRoots_rootOwnCode {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (StagedBodyTrace.settledRoots_rootOwnEntry trace R member).code

theorem ConfiguredBlockTraceIn.settledRoots_rootOwnCode {F : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (ConfiguredBlockTraceIn.settledRoots_rootOwnEntry trace R member).code

theorem ConfiguredHistoryTraceIn.settledRoots_rootOwnCode {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ R ∈ history.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  exact (ConfiguredHistoryTraceIn.settledRoots_rootOwnEntry history R member).code

/-- The same selected outer root supplies the raw-frame entry facts needed by local consumers. -/
theorem ConfiguredHistoryTraceIn.mem_rawFrames_of_mem_settledRoots {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) (R : Exec.Frame)
    (member : R ∈ history.settledRoots) : Exec.Frame.rootDeriv R ∈ history.rawFrames := by
  apply history.mem_rawFrames_of_mem_settledFrames R
  rw [history.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, member, by
    rw [Exec.Frame.committedFrames_self]
    exact List.mem_cons_self⟩

end Blanc.ExecutionTrace
