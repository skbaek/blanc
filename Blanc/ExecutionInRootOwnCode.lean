import Blanc.ExecutionInRawNodeOrigin
import Blanc.ExecutionInCodeImage

/-! Local own-code at actual complete-settlement outer roots, without installed-world premises. -/

namespace Blanc.ExecutionTrace

open Jaune

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
  rcases trace with ⟨slot, retained, process⟩
  have own := retained.settledRoots_rootOwnCode process
    (processCreateMessage_msg_rootCode collision)
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · exact own R member
    · cases member

/-- Only the actual outer roots are selected; delegated descendants are not included. -/
theorem MessageCallTrace.settledRoots_rootOwnCode {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out) (own : MsgOwn msg) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun target collision evm core inner result =>
    exact inner.settledRoots_rootOwnCode (by simpa only [messageCreateCollision] using collision)
  | callRun target delegated refund delegation execMsg execEq evm core inner result =>
    subst execEq
    exact inner.settledRoots_rootOwnCode
      (messageCallExecutionMessage_rootCode (messageCallDelegation_own delegation target own))

theorem TransactionTrace.settledRoots_rootOwnCode {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) :=
  trace.message.settledRoots_rootOwnCode (prepareMessage_own_entry trace.prepared)

theorem ApplyTransactionsTrace.settledRoots_rootOwnCode
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  induction trace with
  | nil => intro R member; cases member
  | cons head tail ih =>
    intro R member
    rcases List.mem_append.mp member with here | later
    · exact head.settledRoots_rootOwnCode R here
    · exact ih R later

theorem SystemMessageTrace.settledRoots_rootOwnCode {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) :=
  trace.message.settledRoots_rootOwnCode fun _ => ⟨rfl, rfl⟩

theorem RequestsTrace.settledRoots_rootOwnCode {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  rcases List.mem_append.mp member with withdrawal | consolidation
  · exact trace.withdrawal.settledRoots_rootOwnCode R withdrawal
  · exact trace.consolidation.settledRoots_rootOwnCode R consolidation

theorem BeaconStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ message _ _ => exact message.settledRoots_rootOwnCode

theorem HistoryStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ _ _ message _ _ => exact message.settledRoots_rootOwnCode

theorem RequestStageTrace.settledRoots_rootOwnCode {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ requests _ => exact requests.settledRoots_rootOwnCode

theorem StagedBodyTrace.settledRoots_rootOwnCode {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  intro R member
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((beacon | history) | transaction) | request
  · exact trace.beacon.settledRoots_rootOwnCode R beacon
  · exact trace.history.settledRoots_rootOwnCode R history
  · exact trace.transactions.settledRoots_rootOwnCode R transaction
  · exact trace.requests.settledRoots_rootOwnCode R request

theorem ConfiguredBlockTraceIn.settledRoots_rootOwnCode {F : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ R ∈ trace.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) :=
  trace.bodyTrace.settledRoots_rootOwnCode

/-- Every actual settled outer root runs its entry code whenever that code is
nonempty and nondelegating. This conditional equality needs no installed-world
invariant or extra stage capability. -/
theorem ConfiguredHistoryTraceIn.settledRoots_rootOwnCode {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ R ∈ history.settledRoots, RootOwnCode (Exec.Frame.rootDeriv R) := by
  induction history with
  | refl => intro R member; cases member
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with earlier | inBlock
    · exact ih R earlier
    · exact block.settledRoots_rootOwnCode R inBlock

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
