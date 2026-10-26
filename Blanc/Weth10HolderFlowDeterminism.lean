import Blanc.ExecutionTraceDeterminism
import Blanc.Weth10HolderFlow

namespace Blanc

open Jaune

namespace Weth10

theorem RetainedXlot.eq_of_same {xl : Xlot}
    (left right : RetainedXlot xl) : left = right :=
  Blanc.ExecutionTrace.RetainedXlot.eq_of_same left right

/-- A filled retained slot satisfying the deterministic frame wrapper is
uniquely indexed, even though `RunFrame` itself existentially names the raw
child outcome. -/
theorem RetainedXlot.index_eq_of_runFrame
    {f : Jaune.Frame}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {leftSlot rightSlot : Xlot}
    (leftRetained : RetainedXlot leftSlot)
    (rightRetained : RetainedXlot rightSlot)
    (leftRun : RunFrame f leftSlot out)
    (rightRun : RunFrame f rightSlot out) : leftSlot = rightSlot :=
  Blanc.ExecutionTrace.RetainedXlot.index_eq_of_runFrame leftRetained rightRetained leftRun rightRun

theorem ProcessMessageTrace.eq_of_same
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (left right : ProcessMessageTrace msg out) : left = right :=
  Blanc.ExecutionTrace.ProcessMessageTrace.eq_of_same left right

theorem ProcessCreateMessageTrace.eq_of_same
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (left right : ProcessCreateMessageTrace msg out) : left = right :=
  Blanc.ExecutionTrace.ProcessCreateMessageTrace.eq_of_same left right

theorem MessageCallTrace.toResult
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    processMessageCall msg = .ok (state, out) :=
  Blanc.ExecutionTrace.MessageCallTrace.toResult trace

theorem MessageCallTrace.index_eq_of_same_input
    {msg : Msg} {leftState rightState : State}
    {leftOut rightOut : MsgCallOutput}
    (left : MessageCallTrace msg leftState leftOut)
    (right : MessageCallTrace msg rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut :=
  Blanc.ExecutionTrace.MessageCallTrace.index_eq_of_same_input left right

theorem MessageCallTrace.eq_of_same
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (left right : MessageCallTrace msg state out) : left = right :=
  Blanc.ExecutionTrace.MessageCallTrace.eq_of_same left right

theorem MessageCallTrace.index_eq_and_heq_of_same_input
    {msg : Msg} {leftState rightState : State}
    {leftOut rightOut : MsgCallOutput}
    (left : MessageCallTrace msg leftState leftOut)
    (right : MessageCallTrace msg rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut ∧ HEq left right :=
  Blanc.ExecutionTrace.MessageCallTrace.index_eq_and_heq_of_same_input left right

theorem SystemMessageTrace.index_eq_of_same_input
    {benv : Benv} {target : Adr} {data : Bytes}
    {leftState rightState : State} {leftOut rightOut : MsgCallOutput}
    (left : SystemMessageTrace benv target data leftState leftOut)
    (right : SystemMessageTrace benv target data rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut := by
  have hpair : (leftState, leftOut) = (rightState, rightOut) :=
    Except.ok.inj (left.run.symm.trans right.run)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem SystemMessageTrace.eq_of_same
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (left right : SystemMessageTrace benv target data state out) :
    left = right := by
  rcases left with ⟨leftMessage, leftRun⟩
  rcases right with ⟨rightMessage, rightRun⟩
  have hmessage := MessageCallTrace.eq_of_same leftMessage rightMessage
  subst rightMessage
  rfl

theorem SystemMessageTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {target : Adr} {data : Bytes}
    {leftState rightState : State} {leftOut rightOut : MsgCallOutput}
    (left : SystemMessageTrace benv target data leftState leftOut)
    (right : SystemMessageTrace benv target data rightState rightOut) :
    leftState = rightState ∧ leftOut = rightOut ∧ HEq left right := by
  rcases SystemMessageTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (SystemMessageTrace.eq_of_same left right)⟩

theorem TransactionTrace.index_eq_of_same_input
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : TransactionTrace benv bout tx index leftState leftBout)
    (right : TransactionTrace benv bout tx index rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout :=
  Blanc.ExecutionTrace.TransactionTrace.index_eq_of_same_input left right

theorem TransactionTrace.eq_of_same
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (left right : TransactionTrace benv bout tx index state bout') :
    left = right :=
  Blanc.ExecutionTrace.TransactionTrace.eq_of_same left right

theorem TransactionTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : TransactionTrace benv bout tx index leftState leftBout)
    (right : TransactionTrace benv bout tx index rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout ∧ HEq left right :=
  Blanc.ExecutionTrace.TransactionTrace.index_eq_and_heq_of_same_input left right

theorem ApplyTransactionsTrace.toRun
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout
      finalBenv finalBout) :
    applyTransactions txs benv bout = .ok (finalBenv, finalBout) :=
  Blanc.ExecutionTrace.ApplyTransactionsTrace.toRun trace

theorem ApplyTransactionsTrace.index_eq_of_same_input
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {leftBenv rightBenv : Benv} {leftBout rightBout : BlockOutput}
    (left : ApplyTransactionsTrace txs benv bout leftBenv leftBout)
    (right : ApplyTransactionsTrace txs benv bout rightBenv rightBout) :
    leftBenv = rightBenv ∧ leftBout = rightBout :=
  Blanc.ExecutionTrace.ApplyTransactionsTrace.index_eq_of_same_input left right

theorem ApplyTransactionsTrace.eq_of_same
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (left right : ApplyTransactionsTrace txs benv bout
      finalBenv finalBout) : left = right :=
  Blanc.ExecutionTrace.ApplyTransactionsTrace.eq_of_same left right

theorem RequestsTrace.index_eq_of_same_input
    {benv : Benv} {bout : BlockOutput}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : RequestsTrace benv bout leftState leftBout)
    (right : RequestsTrace benv bout rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout := by
  have hpair : (leftState, leftBout) = (rightState, rightBout) :=
    Except.ok.inj (left.run.symm.trans right.run)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem RequestsTrace.eq_of_same
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (left right : RequestsTrace benv bout state bout') : left = right := by
  rcases left with ⟨ldeposits, lparsed, _, lwState, lwOut, _, lwTrace, lcState, lcOut, _,
    lcTrace, _⟩
  rcases right with ⟨rdeposits, rparsed, _, rwState, rwOut, _, rwTrace, rcState, rcOut, _,
    rcTrace, _⟩
  have hdeposits : ldeposits = rdeposits := Except.ok.inj (lparsed.symm.trans rparsed)
  subst hdeposits
  obtain ⟨rfl, rfl, hwithdrawal⟩ :=
    SystemMessageTrace.index_eq_and_heq_of_same_input lwTrace rwTrace
  cases hwithdrawal
  obtain ⟨rfl, rfl, hconsolidation⟩ :=
    SystemMessageTrace.index_eq_and_heq_of_same_input lcTrace rcTrace
  cases hconsolidation
  rfl

theorem RequestsTrace.index_eq_and_heq_of_same_input
    {benv : Benv} {bout : BlockOutput}
    {leftState rightState : State}
    {leftBout rightBout : BlockOutput}
    (left : RequestsTrace benv bout leftState leftBout)
    (right : RequestsTrace benv bout rightState rightBout) :
    leftState = rightState ∧ leftBout = rightBout ∧ HEq left right := by
  rcases RequestsTrace.index_eq_of_same_input left right with
    ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, heq_of_eq (RequestsTrace.eq_of_same left right)⟩

theorem AppliedBodyTrace.eq_of_same
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (left right : AppliedBodyTrace benv txs ommers wds state bout) :
    left = right := by
  rcases left with ⟨leftRun, leftBeaconState, leftBeaconOut, leftBeacon,
    leftLastHash, leftLastHashRun, leftHistoryState, leftHistoryOut,
    leftHistory, leftDecodedTxs, leftDecodeRun, leftTransactionBenv,
    leftTransactionBout, leftTransactions, leftRequestState, leftRequestBout,
    leftRequests, leftRequestStateEq, leftRequestBoutEq⟩
  rcases right with ⟨rightRun, rightBeaconState, rightBeaconOut, rightBeacon,
    rightLastHash, rightLastHashRun, rightHistoryState, rightHistoryOut,
    rightHistory, rightDecodedTxs, rightDecodeRun, rightTransactionBenv,
    rightTransactionBout, rightTransactions, rightRequestState, rightRequestBout,
    rightRequests, rightRequestStateEq, rightRequestBoutEq⟩
  rcases SystemMessageTrace.index_eq_of_same_input leftBeacon rightBeacon with
    ⟨hBeaconState, hBeaconOut⟩
  subst rightBeaconState
  subst rightBeaconOut
  have hBeacon := SystemMessageTrace.eq_of_same leftBeacon rightBeacon
  subst rightBeacon
  have hLastHash : leftLastHash = rightLastHash :=
    Except.ok.inj (leftLastHashRun.symm.trans rightLastHashRun)
  subst rightLastHash
  rcases SystemMessageTrace.index_eq_of_same_input leftHistory rightHistory with
    ⟨hHistoryState, hHistoryOut⟩
  subst rightHistoryState
  subst rightHistoryOut
  have hHistory := SystemMessageTrace.eq_of_same leftHistory rightHistory
  subst rightHistory
  have hDecodedTxs : leftDecodedTxs = rightDecodedTxs :=
    Except.ok.inj (leftDecodeRun.symm.trans rightDecodeRun)
  subst rightDecodedTxs
  rcases ApplyTransactionsTrace.index_eq_of_same_input
    leftTransactions rightTransactions with
    ⟨hTransactionBenv, hTransactionBout⟩
  subst rightTransactionBenv
  subst rightTransactionBout
  have hTransactions :=
    ApplyTransactionsTrace.eq_of_same leftTransactions rightTransactions
  subst rightTransactions
  obtain ⟨hRequestState, hRequestBout, hRequests⟩ :=
    RequestsTrace.index_eq_and_heq_of_same_input leftRequests rightRequests
  cases hRequestState
  cases hRequestBout
  cases hRequests
  rfl

/-- For fixed endpoints, the applied block determines all retained replay and
flow data. -/
theorem AccountedBlock.eq_of_block_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (left right : AccountedBlock cfg dp ca pre post)
    (hblock : left.block = right.block) : left = right := by
  rcases left with ⟨lblock, _, lfork, lforkAt, lrules, _, lrulesAt, _, _, lbodyState,
    lblockOutput, lbodyRun, lbodyTrace, lactions, lactionsEq, lobservations, lobservationsEq, _⟩
  rcases right with ⟨rblock, _, rfork, rforkAt, rrules, _, rrulesAt, _, _, rbodyState,
    rblockOutput, rbodyRun, rbodyTrace, ractions, ractionsEq, robservations, robservationsEq, _⟩
  change lblock = rblock at hblock
  subst hblock
  have hfork : lfork = rfork := Except.ok.inj (lforkAt.symm.trans rforkAt)
  subst hfork
  have hrules : lrules = rrules := Except.ok.inj (lrulesAt.symm.trans rrulesAt)
  subst hrules
  have hbody : (lbodyState, lblockOutput) = (rbodyState, rblockOutput) :=
    Except.ok.inj (lbodyRun.symm.trans rbodyRun)
  cases hbody
  have htrace := AppliedBodyTrace.eq_of_same lbodyTrace rbodyTrace
  subst htrace
  subst lactionsEq
  subst ractionsEq
  subst lobservationsEq
  subst robservationsEq
  rfl

theorem AccountedBlock.observations_eq_of_block_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (left right : AccountedBlock cfg dp ca pre post)
    (hblock : left.block = right.block) :
    left.observations = right.observations := by
  rw [AccountedBlock.eq_of_block_eq left right hblock]

private theorem append_singleton_eq_append_singleton
    {α : Type} {leftPrefix rightPrefix : List α} {leftLast rightLast : α}
    (h : leftPrefix ++ [leftLast] = rightPrefix ++ [rightLast]) :
    leftPrefix = rightPrefix ∧ leftLast = rightLast := by
  have reversed : leftLast :: leftPrefix.reverse =
      rightLast :: rightPrefix.reverse := by
    simpa only [List.cons.injEq, List.reverse_inj, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append] using congrArg List.reverse h
  exact ⟨List.reverse_injective (List.cons.inj reversed).2,
    (List.cons.inj reversed).1⟩

/-- Replaying the same block list from a fixed checkpoint has a unique
endpoint. -/
theorem AccountedHistory.endpoint_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint leftFuture rightFuture : BlockChain}
    (left : AccountedHistory cfg dp ca checkpoint leftFuture)
    (right : AccountedHistory cfg dp ca checkpoint rightFuture)
    (hblocks : left.appliedBlocks = right.appliedBlocks) :
    leftFuture = rightFuture := by
  induction left generalizing rightFuture with
  | refl hcfg hctx hid =>
      cases right with
      | refl => rfl
      | step prior accounted =>
          simp only [appliedBlocks, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self,
            and_false] at hblocks
  | step prior leftBlock ih =>
      cases right with
      | refl =>
          simp only [appliedBlocks, List.append_eq_nil_iff, List.cons_ne_self, and_false] at hblocks
      | step rightPrior rightBlock =>
          change prior.appliedBlocks ++ [leftBlock.block] =
            rightPrior.appliedBlocks ++ [rightBlock.block] at hblocks
          rcases append_singleton_eq_append_singleton hblocks with
            ⟨hprior, hblock⟩
          have hcurrent := ih rightPrior hprior
          have hsame := congrArg₂
            (stateTransitionUsing cfg)
            hcurrent hblock
          exact Except.ok.inj
            (leftBlock.transition.symm.trans
              (hsame.trans rightBlock.transition))

theorem AccountedHistory.flowObservations_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (left right : AccountedHistory cfg dp ca checkpoint future)
    (hblocks : left.appliedBlocks = right.appliedBlocks) :
    left.flowObservations = right.flowObservations := by
  induction left with
  | refl hcfg hctx hid =>
      cases right with
      | refl => rfl
      | step prior accounted =>
          simp only [appliedBlocks, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self,
            and_false] at hblocks
  | step prior leftBlock ih =>
      cases right with
      | refl =>
          simp only [appliedBlocks, List.append_eq_nil_iff, List.cons_ne_self, and_false] at hblocks
      | step rightPrior rightBlock =>
          change prior.appliedBlocks ++ [leftBlock.block] =
            rightPrior.appliedBlocks ++ [rightBlock.block] at hblocks
          rcases append_singleton_eq_append_singleton hblocks with
            ⟨hprior, hblock⟩
          have hcurrent :=
            AccountedHistory.endpoint_eq_of_appliedBlocks_eq
              prior rightPrior hprior
          cases hcurrent
          have hprefix := ih rightPrior hprior
          have hlast :=
            AccountedBlock.observations_eq_of_block_eq
              leftBlock rightBlock hblock
          simp only [AccountedHistory.flowObservations]
          rw [hprefix, hlast]

theorem AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history₁ history₂ :
      AccountedHistory cfg dp ca checkpoint future)
    (hblocks : history₁.appliedBlocks = history₂.appliedBlocks) :
    history₁.weth10Flow u = history₂.weth10Flow u := by
  unfold AccountedHistory.weth10Flow
  rw [AccountedHistory.flowObservations_eq_of_appliedBlocks_eq
    history₁ history₂ hblocks]

end Weth10

end Blanc
