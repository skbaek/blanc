-- ExecutionAccountingLadder.lean : the contract-neutral wrapper ladder over an
-- accounting replay.
--
-- `ExecutionAccountingReplay` owns the settlement seams of one retained
-- message.  Above them, every contract that interprets a retained history as
-- an ordered replay climbs the same ladder: message, CREATE, message-call
-- wrapper, transaction, transaction list, system message, request calls,
-- direct withdrawals, block body, configured block, configured history.  None
-- of those rungs is about a ledger.  A contract supplies an `AccountingLadder`
-- -- its account-local carrier, the carrier's composition law, the tag its
-- produced credit steps carry, the replay of one retained message root, and its
-- `ContractSpec` preservation -- and receives every rung at its own vocabulary.
--
-- The world word bound is an explicit premise up to the request rung and is
-- derived above it, because a general `ContractSpec.Side` need not be `SumNof`.

import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionTraceFresh
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionTraceSettledFrames

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

/-! ## 2.3 The ladder interface -/

/-- Everything the wrapper ladder needs from one contract, and nothing else.

* `carrier` — the account-local replay interpretation;
* `append` — replays compose at a shared boundary (the one law of the replay
  relation the seams never needed);
* `tag` — the provenance a credit step produced at ladder level carries,
  given the block and transaction position (`Unit`-valued carriers ignore it);
* `root` — a committed retained execution at the EVM root of a successful
  message entry replays from the frame's entry boundary to its committed
  post-state, for every message that is run-ready for `S`, is not a direct
  self-call, opens below the word bound, and enters a covered runtime fork.
  This is exactly the shape of a
  contract's `lift_core` instance at `initEvm`;
* `preserves` — the contract's `ContractSpec` preservation, which the generic
  ladder lemmas consume to carry `S.StateInv` along the history. -/
structure AccountingLadder (S : ContractSpec) (ca : Adr) where
  carrier : ReplayCarrier ca
  append : ∀ {pre mid post : carrier.Snap} {left right : List carrier.Step},
    carrier.Replay pre left mid → carrier.Replay mid right post →
      carrier.Replay pre (left ++ right) post
  tag : Nat → Option Nat → carrier.Tag
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entry : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution},
    Exec pc sevm pre out →
    msg.benvAfterTransfer = .ok entry →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry) →
    ∀ committed : Execution.commits out = true,
    S.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    CoveredFork sevm.benvStat.fork →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, carrier.Replay (carrier.frameEntry sevm pre.state) steps
      (carrier.ofState (Execution.committedPost out committed).state)
  preserves : S.Preserves ca

/-! ## 2.3' The observed ladder

An `Observed` ladder is a ladder together with an observation of its carrier's
step lists and a root law that observes exactly each covered root's committed frames.
The observed proof engine lives in `ExecutionAccountingAdmission`; the rungs
below preserve the original interface by supplying automatic fresh entry. The
unobserved rungs of §2.4 read them through `Observed.trivial`, observing nothing. -/

namespace AccountingLadder

/-- A ladder with an observation of its steps whose root replay observes
exactly the root's committed frames. -/
structure Observed {S : ContractSpec} {ca : Adr} (L : AccountingLadder S ca) where
  view : ReplayObservation L.carrier
  root : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entry : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out),
    msg.benvAfterTransfer = .ok entry →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entry) →
    ∀ committed : Execution.commits out = true,
    S.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    CoveredFork sevm.benvStat.fork →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∃ steps, L.carrier.Replay (L.carrier.frameEntry sevm pre.state) steps
      (L.carrier.ofState (Execution.committedPost out committed).state) ∧
      view.obs steps = (Exec.committedFrames run).flatMap view.frameObs

namespace Observed

variable {S : ContractSpec} {ca : Adr} {L : AccountingLadder S ca}

/-- Every ladder is observed by the observation that sees nothing. -/
def trivial (L : AccountingLadder S ca) : L.Observed where
  view := ReplayObservation.trivial L.carrier
  root := by
    intro blockIndex transactionIndex msg entry pc sevm pre out run transfer
      evmEq committed runReady callerNe hfork sumNof
    exact (L.root blockIndex transactionIndex run transfer evmEq committed
      runReady callerNe hfork sumNof).imp fun _ replay =>
        ⟨replay, by simp only [ReplayObservation.trivial, List.nil_eq, List.flatMap_eq_nil_iff,
          implies_true]⟩

/-- The ordinary source-program ladder is the semantic admitted ladder with
fresh entry supplied by the retained trace itself. Existing root and frame
preservation laws need no admission premise. -/
def toAdmitted (O : L.Observed) : AccountingLadderAdmitted S.toSem ca Exec.FreshEntry where
  carrier := L.carrier
  append := L.append
  tag := L.tag
  preserves := by
    intro sevm pre post hfork run _admitted code memory inv
    exact ContractSpec.preserves_toSem L.preserves sevm pre post hfork run code memory inv
  view := O.view
  root := by
    intro blockIndex transactionIndex msg entry pc sevm pre out run transfer
      evmEq committed _admitted runReady callerNe hfork sumNof
    exact O.root blockIndex transactionIndex run transfer evmEq committed
      ⟨ContractSpec.msgInv_ofSem runReady.ready, runReady.codeOrForeign⟩
      callerNe hfork sumNof

/-- G1, observed. -/
theorem processMessage (O : L.Observed)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.processMessage trace (trace.freshFrameAdmitted ca)
    ⟨ContractSpec.msgInv_toSem runReady.ready, runReady.codeOrForeign⟩
    callerNe hfork sumNof blockIndex transactionIndex

/-- G2, observed. -/
theorem processCreateMessage (O : L.Observed)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.processCreateMessage trace (trace.freshFrameAdmitted ca)
    ⟨ContractSpec.msgInv_toSem runReady.ready, runReady.codeOrForeign⟩
    hfork sumNof targetNone targetNe fresh blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in

/-- G3, observed. -/
theorem messageCall (O : L.Observed)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.messageCall trace (trace.freshFrameAdmitted ca)
    ⟨ContractSpec.msgInv_toSem runReady.ready, runReady.codeOrForeign⟩
    callerNe hfork sumNof blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in

/-- G3', observed. -/
theorem transactionMessage (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : S.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.transactionMessage trace (trace.freshFrameAdmitted ca)
    (ContractSpec.msgInv_toSem msgInv) sumNof hfork blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in

/-- G4, observed: the two gas credits are observed as nothing. -/
theorem transaction (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.transaction trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) notCreated sumNof hfork blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in

/-- G5, observed. -/
theorem transactionList (O : L.Observed)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.transactionList trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) notCreated sumNof hfork blockIndex

open _root_.Blanc.ExecutionTrace in

/-- G6, observed. -/
theorem systemMessage (O : L.Observed)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.systemMessage trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) notCreated systemNe sumNof hfork blockIndex

open _root_.Blanc.ExecutionTrace in

/-- G7, observed. -/
theorem requests (O : L.Observed)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.requests trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) notCreated sumNof hfork blockIndex

open _root_.Blanc.ExecutionTrace in

/-- G8, observed: direct withdrawals are observed as nothing. -/
theorem directWithdrawal (O : L.Observed)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) ∧
      O.view.obs steps = [] := by
  exact O.toAdmitted.directWithdrawal pre wds bound blockIndex

open _root_.Blanc.ExecutionTrace in

/-- G9, observed: the segments are observed in `applyBody` order. -/
theorem body (O : L.Observed)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.body trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) notCreated bound hfork blockIndex

/-- G10, observed. -/
theorem configuredBlock (O : L.Observed)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : S.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) ∧
      O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs := by
  exact O.toAdmitted.configuredBlock trace (trace.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv) blockIndex

/-- G11, observed: a whole configured history replays with exactly the
observations of its settled frames, in chain order. -/
theorem configuredHistory (O : L.Observed) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : S.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
        (L.carrier.ofState future.state) ∧
      O.view.obs steps = history.settledFrames.flatMap O.view.frameObs := by
  let _ := hcov
  exact O.toAdmitted.configuredHistory history (history.freshFrameAdmitted ca)
    (ContractSpec.stateInv_toSem inv)

end Observed

end AccountingLadder

namespace AccountingLadder

variable {S : ContractSpec} {ca : Adr}

/-! ## 2.4 The rungs -/

/-- G1.  One retained CALL message. -/
theorem processMessage (L : AccountingLadder S ca)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).processMessage trace runReady callerNe hfork sumNof blockIndex transactionIndex).imp
    fun _ replay => replay.1

/-- G2.  One retained CREATE constructor at a fresh foreign address. -/
theorem processCreateMessage (L : AccountingLadder S ca)
    {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (runReady : S.MessageRunReady ca msg)
    (hfork : CoveredFork msg.benv.stat.fork)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).processCreateMessage trace runReady hfork sumNof targetNone targetNe fresh blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G3.  The settled message-call wrapper (create collision, CREATE run, and
EIP-7702-normalized call). -/
theorem messageCall (L : AccountingLadder S ca)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (runReady : S.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork msg.benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState msg.benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).messageCall trace runReady callerNe hfork sumNof blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G3'.  A transaction's prepared message, including the create-at-`ca` case,
which the collision test turns into a no-op. -/
theorem transactionMessage (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : S.MsgInv ca trace.msg)
    (sumNof : sum trace.msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState trace.msg.benv.state) steps
      (L.carrier.ofState trace.messageState) := by
  exact ((Observed.trivial L).transactionMessage trace msgInv sumNof hfork blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G4.  One whole retained transaction. -/
theorem transaction (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).transaction trace inv notCreated sumNof hfork blockIndex transactionIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G5.  A retained transaction list. -/
theorem transactionList (L : AccountingLadder S ca)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState finalBenv.state) := by
  exact ((Observed.trivial L).transactionList trace inv notCreated sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G6.  One retained system message. -/
theorem systemMessage (L : AccountingLadder S ca)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).systemMessage trace inv notCreated systemNe sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G7.  The two checked request calls. -/
theorem requests (L : AccountingLadder S ca)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).requests trace inv notCreated sumNof hfork blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G8.  The direct consensus withdrawals. -/
theorem directWithdrawal (L : AccountingLadder S ca)
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre) steps
      (L.carrier.ofState (processWithdrawalsState pre wds)) := by
  exact ((Observed.trivial L).directWithdrawal pre wds bound blockIndex).imp
    fun _ replay => replay.1

open _root_.Blanc.ExecutionTrace in
/-- G9.  A whole successful block body, in `applyBody` order. -/
theorem body (L : AccountingLadder S ca)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : S.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState benv.state) steps
      (L.carrier.ofState state) := by
  exact ((Observed.trivial L).body trace inv notCreated bound hfork blockIndex).imp
    fun _ replay => replay.1

/-- G10.  A whole configured block.  The word bound comes from the block's own
`openingBound`, so the rung asks only for the state invariant. -/
theorem configuredBlock (L : AccountingLadder S ca)
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : S.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState pre.state) steps
      (L.carrier.ofState post.state) := by
  exact ((Observed.trivial L).configuredBlock trace inv blockIndex).imp
    fun _ replay => replay.1

/-- G11.  A whole configured history; each block is tagged with its header
number. -/
theorem configuredHistory (L : AccountingLadder S ca)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : S.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
      (L.carrier.ofState future.state) := by
  exact ((Observed.trivial L).configuredHistory history inv hcov).imp
    fun _ replay => replay.1

end AccountingLadder

/-! ## 2.5 The block-structured history carrier

`L.TraceRealizes cfg root steps future` supplements configured reachability from
`root` with the replay steps the chain actually produced: in chain order, one
retained `ConfiguredBlockTrace` per imported block together with that block's
own replay segment, the whole step list being their concatenation.  The
carrier names no contract; the two contract facts it needs -- the root's
reflexive configured reach and the contract invariant at the root -- enter as
arguments of the lemmas that use them. -/

namespace AccountingLadder

variable {S : ContractSpec} {ca : Adr}

inductive TraceRealizes (L : AccountingLadder S ca) (cfg : ChainConfig)
    (root : BlockChain) : List L.carrier.Step → BlockChain → Prop where
  | refl : TraceRealizes L cfg root [] root
  | step {current future : BlockChain}
      {priorSteps blockSteps : List L.carrier.Step}
      (prior : TraceRealizes L cfg root priorSteps current)
      (block : _root_.Blanc.ExecutionTrace.ConfiguredBlockTrace cfg current future)
      (replay : L.carrier.Replay (L.carrier.ofState current.state) blockSteps
        (L.carrier.ofState future.state)) :
      TraceRealizes L cfg root (priorSteps ++ blockSteps) future
-- mirrors ProrataAccountingHistory.lean:96–107.

/-- Every retained configured history from an invariant-satisfying root is
realized, with exactly the observations of its settled frames in chain order. -/
theorem Observed.traceRealizes_of_configuredHistoryTrace
    {L : AccountingLadder S ca} (O : L.Observed)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future ∧
      O.view.obs steps = history.settledFrames.flatMap O.view.frameObs := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], .refl, by simpa only [ExecutionTrace.ConfiguredHistoryTrace.settledFrames,
    List.flatMap_nil] using O.view.obs_nil⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorRealizes, priorObserved⟩ := ih
      obtain ⟨blockSteps, blockReplay, blockObserved⟩ :=
        O.configuredBlock block (prior.stateInv L.preserves inv hcov)
          block.block.header.number
      refine ⟨priorSteps ++ blockSteps, .step priorRealizes block blockReplay, ?_⟩
      rw [O.view.obs_append, priorObserved, blockObserved]
      simp only [ExecutionTrace.ConfiguredBlockTrace.settledFrames,
        ExecutionTrace.AppliedBodyTrace.settledFrames,
        ExecutionTrace.SystemMessageTrace.settledFrames,
        ExecutionTrace.MessageCallTrace.settledFrames,
        ExecutionTrace.ProcessCreateMessageTrace.settledFrames, ExceptT.stM_eq,
        ExecutionTrace.ProcessMessageTrace.settledFrames, List.append_assoc,
        ExecutionTrace.RequestsTrace.settledFrames, List.flatMap_append,
        ExecutionTrace.ConfiguredHistoryTrace.settledFrames]
-- mirrors ProrataAccountingHistory.lean:146–159, carrying the observation.

namespace TraceRealizes

/-- Every realized trace projects to the configured chain reach it replays. -/
theorem toReachUsing {L : AccountingLadder S ca} {cfg : ChainConfig}
    {root future : BlockChain} {steps : List L.carrier.Step}
    (rootReach : BlockChain.ReachUsing cfg root root)
    (realizes : L.TraceRealizes cfg root steps future) :
    BlockChain.ReachUsing cfg root future := by
  induction realizes with
  | refl => exact rootReach
  | step prior block replay ih => exact .step ih block.bound block.transition
-- mirrors ProrataAccountingHistory.lean:116–123; `root.reflReach` → `rootReach`.

/-- The realized steps are one connected replay from the root to the
continuation, the per-block segments concatenated in chain order. -/
theorem toReplay {L : AccountingLadder S ca} {cfg : ChainConfig}
    {root future : BlockChain} {steps : List L.carrier.Step}
    (realizes : L.TraceRealizes cfg root steps future) :
    L.carrier.Replay (L.carrier.ofState root.state) steps
      (L.carrier.ofState future.state) := by
  induction realizes with
  | refl => exact L.carrier.nil _
  | step prior block replay ih => exact L.append ih replay
-- mirrors ProrataAccountingHistory.lean:128–137.

/-- Every retained configured history from an invariant-satisfying root is
realized; each block is tagged with its own header number. -/
theorem of_configuredHistoryTrace (L : AccountingLadder S ca)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (history : _root_.Blanc.ExecutionTrace.ConfiguredHistoryTrace cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future := by
  exact ((Observed.trivial L).traceRealizes_of_configuredHistoryTrace inv
    history hcov).imp fun _ realizes => realizes.1

/-- Configured reachability from an invariant-satisfying root is never more
permissive than the carrier. -/
theorem exists_of_reachUsing (L : AccountingLadder S ca)
    {cfg : ChainConfig} {root future : BlockChain}
    (inv : S.StateInv ca root.state)
    (reach : BlockChain.ReachUsing cfg root future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, L.TraceRealizes cfg root steps future := by
  rcases _root_.Blanc.ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing
    reach (by intro _ _ _ _ _ hfork; exact hcov _ _ hfork) with ⟨history⟩
  exact of_configuredHistoryTrace L inv history hcov
-- mirrors ProrataAccountingHistory.lean:167–173.

end TraceRealizes

end AccountingLadder

end ExecutionAccountingReplay

end Blanc
