import Blanc.ExecutionSenderOccurrences
import Blanc.ExecutionTraceRootCallers
import Blanc.ExecutionInCodeImage

/-!
# Root caller exclusion from the actual admitted senders

Transaction roots carry their checked sender; canonical system roots carry systemAddress.
The actual sender-query exclusion therefore excludes an address from every settled root
on any selected fork domain, including histories whose VM calls revert.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A transaction root's caller is its actual admitted sender. -/
theorem TransactionTrace.settledRoots_caller_ne_of_sender {a : Adr} {benv : Benv}
    {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (sender : trace.sender ≠ a) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a := by
  intro R member
  rw [trace.message.settledRoots_caller R member, trace.msg_caller]
  exact sender

/-- The actual head/tail sender fold excludes callers of the transaction roots. -/
theorem ApplyTransactionsTrace.settledRoots_caller_ne_of_noSenderAt {a : Adr}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (senders : trace.NoSenderAt a) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a := by
  induction trace with
  | nil => intro R member; cases member
  | cons head tail ih =>
    intro R member
    rcases List.mem_append.mp member with here | later
    · exact head.settledRoots_caller_ne_of_sender senders.1 R here
    · exact ih senders.2 R later

/-- Skipped beacon stages have no roots; called stages use the canonical system caller. -/
theorem BeaconStageTrace.settledRoots_caller {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ message _ _ => exact message.settledRoots_caller

/-- Optional history-storage roots carry the canonical system caller. -/
theorem HistoryStageTrace.settledRoots_caller {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ _ _ _ message _ _ => exact message.settledRoots_caller

/-- Optional request roots carry the canonical system caller. -/
theorem RequestStageTrace.settledRoots_caller {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    ∀ R ∈ trace.settledRoots, R.sevm.caller = systemAddress := by
  cases trace with
  | skipped => intro R member; cases member
  | called _ requests _ => exact requests.settledRoots_caller

/-- Sender exclusion and a distinct system address cover every optional body stage. -/
theorem StagedBodyTrace.settledRoots_caller_ne_of_noSenderAt {a : Adr} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (senders : trace.transactions.NoSenderAt a) (notSystem : a ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a := by
  intro R member
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((beacon | history) | transaction) | request
  · rw [trace.beacon.settledRoots_caller R beacon]
    exact Ne.symm notSystem
  · rw [trace.history.settledRoots_caller R history]
    exact Ne.symm notSystem
  · exact trace.transactions.settledRoots_caller_ne_of_noSenderAt senders R transaction
  · rw [trace.requests.settledRoots_caller R request]
    exact Ne.symm notSystem

/-- On any selected fork domain, actual sender exclusion and a distinct system address
exclude the address from every settled message root. -/
theorem ConfiguredHistoryTraceIn.settledRoots_caller_ne_of_noSenderAt
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {a : Adr}
    (senders : history.NoSenderAt a) (notSystem : a ≠ systemAddress) :
    ∀ R ∈ history.settledRoots, R.sevm.caller ≠ a := by
  induction history with
  | refl => intro R member; cases member
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with earlier | inBlock
    · exact ih senders.1 R earlier
    · exact block.bodyTrace.settledRoots_caller_ne_of_noSenderAt senders.2 notSystem R inBlock

/-- Exact-query exclusion on all actual admitted transactions supplies root caller exclusion.
The query population and its original occurrence witnesses are those of senderQueries. -/
theorem ConfiguredHistoryTraceIn.settledRoots_caller_ne_of_senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) {a : Adr}
    (excluded : ∀ query ∈ history.senderQueries, query.recover ≠ .ok a)
    (notSystem : a ≠ systemAddress) :
    ∀ R ∈ history.settledRoots, R.sevm.caller ≠ a :=
  history.settledRoots_caller_ne_of_noSenderAt
    (history.noSenderAt_of_senderQueries excluded) notSystem

end Blanc.ExecutionTrace
